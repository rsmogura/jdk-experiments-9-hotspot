#ifndef HOTSPOT_BUFFERSIZEPREDICTOR_HPP
#define HOTSPOT_BUFFERSIZEPREDICTOR_HPP

#include "memory/allocation.hpp"
#include "ci/ciMethod.hpp"
#include "ci/ciMethodData.hpp"

/** Performs optimisation of buffer size for classes like StringBuilder, ByteArrayOutputStream, and so on.
 *
 * To understand general concepts, consider following graph
 *
 * alloc StringBuilder    kept in InjectionPoint class as 'target_alloc', an optimisation root
 *  |- invokespecial      (new StringBuilder())
 *  |   |- invokespecial  (new StringBuilder(16)), deeper inlining is not important right now
 *  |                     The value 16 is kept as target_value in InjectionPoint
 *  |- invokevirtual      append("Something))
 *  |  |- invokevirtual   (Chained call append("Something").append("."))
 *  |  |- invokevirtual   (Chained call append(...).append(...).toString) has AverageData
 *  |- invokevirtual      toString
 *
 *  The 'optimisations' for given compilation are grouped in InjectionPoints which are uniquely
 *  identified by object allocations (NewInstance / AllocateNode). Each InjectionPoint has
 *  const_value, which is a node representing default size used by default constructor.
 *  The const_value is later replaced by profiled size.
 *
 *  With each InjectionPoint BCIs representing "finish" (or "terminating") methods with their
 *  caller method are associated (FinishMethodPoint). Due to inlining strict invocation nodes
 *  for such methods may not exist and caller may be different then actually compiled
 *  top-level method (deep inline). The finish methods are methods like toString(),
 *  toByteArray(), toCharArray() and there can be zero, one or more of such associations.
 *
 *  At the end and when invoked, for each InjectionPoint, predictor collects AverageData for
 *  associated finish points, calculates new size, and replaces const_vale with
 *  hopefully calculated better size.
 *
 *  As this class is intended to provide generic functionality for C1 & C2, it's parametrised and
 *  subclassable, to fit particular node types, allocations, etc.
 *
 *  This class do not profile AverageData - it just consumes those date and helps to replace
 *  buffers with better size :)
 *
 *  @param A class of allocation node (NewInstance for C1, AllocationNode for C2)
 *  @param C class of constant to replace (Constant for C1, ConNode for C2)
 */
template <class A, class C>
class BufferSizePredictor {
public:
	class FinishPoint;
	class InjectionPoint;
private:
		GrowableArray<InjectionPoint*> _injection_points;
protected:
		/// Designed to be overriden by subclasses to change compilation graph
		virtual void profile_injection_point(InjectionPoint* point, int size_new) = 0;

public:
		BufferSizePredictor() : _injection_points(1) { }


		InjectionPoint* add_injection_point(A* target, C* const_value) {
			InjectionPoint* result = new InjectionPoint(target, const_value);
			_injection_points.append(result);
			return result;
		}


		InjectionPoint* find_injection_point(A* allocation) {
			for (GrowableArrayIterator<InjectionPoint*> i = _injection_points.begin();
			     i != _injection_points.end(); ++i) {
				if ((*i)->allocation() == allocation)
					return *i;
			}

			return NULL;
		}

		//------------------------------------------------------------
		//------             GATHERING STATISTICS               ------
		//------------------------------------------------------------

		/// Adds finish point for given allocation. Searches for
		/// InjectionPoint represented by passed allocation
		bool add_finish_point(A *allocation, ciMethod *method, int bci) {
			assert(method != NULL && bci != -1, "sanity");

			InjectionPoint* point = find_injection_point(allocation);
			if (point == NULL)
				return false;
			point->add_stats(method, bci);

			return true;
		}

		/// Checks if given method is default initializer of one of supported classes
		bool is_profiled_class_initializer(ciMethod* initializer) {
			return vmBufferProfiledClass::profiled_class_by_initializer(initializer->intrinsic_id()) != NULL;
		}

		/// Checks if given method is finish method of one of supported classes
		inline bool is_profiled_class_finish_meth(ciMethod* finish_method) {
			return vmBufferProfiledClass::profiled_class_by_finish_meth(finish_method->intrinsic_id()) != NULL;
		}

		/// Get expected size of buffer when default constructor is called
		/// Mainly used for assertions
		int expected_size_for_initializer(ciMethod* initializer) {
			vmIntrinsics::ID initializer_id = initializer->intrinsic_id();
			vmBufferProfiledClass* prof_class = vmBufferProfiledClass::profiled_class_by_initializer(initializer_id);

			assert(prof_class, "Should be called for well known initializers");
			return prof_class->default_buffer_size();
		}

		//------------------------------------------------------------
		//------ PROFILING FINALIZATION - REPLACE DEFAULT SIZE  ------
		//------------------------------------------------------------

		/// Checks if there is something to profile
		bool has_work() { return _injection_points.length(); }

		/// Goes through all injection points to gather cumulative statistics,
		/// calculate new size, and to replace those in compiler graph
		void do_all_points() {
			if (!has_work())
				return;

			GrowableArrayIterator<InjectionPoint*> i = _injection_points.begin();
			for (; i != _injection_points.end(); ++i) {
				InjectionPoint* injection_point = *i;
				int size_new;
				if (should_profile_point(injection_point, size_new)) {
					profile_injection_point(injection_point, size_new);
				}
			}
		}

		/// Gather statistics for given InjectionPoint and and returns
		/// if point should be profiled, returns new value for size
		bool should_profile_point(InjectionPoint* point, int& size) {
			// Accumulates gathered values
			long sum = 0, count = 0;
			int found_stats = 0;
			jint max = min_jint;

			GrowableArrayIterator<FinishPoint*> i = point->_finish_points.begin();
			for (; i != point->_finish_points.end(); ++i) {
				FinishPoint* finish_point = *i;
				ciMethod* m = finish_point->method();

				if (m->ensure_method_data() && m->method_data()) {
					ciProfileData* profileData = m->method_data()->bci_to_aux_data(
									finish_point->bci(), DataLayout::average_data_tag);
					if (profileData == NULL)
						continue;

					AverageData* averageData = profileData->as_AverageData();
					int  avg_count = averageData->avg_count();
					long avg_sum   = averageData->avg_sum();
					if (count + avg_count < count || sum + avg_sum < sum)
						continue; // Overflow

					count += averageData->avg_count();
					sum += averageData->avg_sum();
					max = MAX2(max, averageData->avg_max());
				}else {
					tty->print("Can't ensure method data at bci %d in method ", finish_point->bci());
					finish_point->method()->print_name(tty);
					tty->print("\n");
				}

				found_stats++;
			}

			// Do profiling if gathered enaugh stats and those are relable
			if (sum > 0 && count > 10) {
				int avg  = sum / count;

				// Grow array to fill the object alignment, it cost no memory, but can help
				// TODO Add information about alignin memory to vmBufferClassInfo
				size = align_size_up(avg, HeapWordSize);
				if (max > 0)
					size = MIN2(size, max);

				return true;
			}else {
//				tty->print("In method "); point->optimised_method()->print_name(tty);
//				tty->print(" injection point has been found and %d possible stats, sum is %ld and count %d."
//								           " Probably method data not loaded.\n", found_stats, sum, count);
				//if (point->_finish_points.length() > 0)
				//point->_finish_points.at(0)->method()->method_data()->print_data_on(tty);

				return false;
			}
		}
		void* operator new(size_t x) throw();
};

/** The common point for class initialization and finish method(s) */
template <class A, class C>
class BufferSizePredictor<A,C>::InjectionPoint {
		friend class BufferSizePredictor;
private:
	C* _const_value;
	A* _allocation;
protected:
	GrowableArray<FinishPoint*> _finish_points;
	ciMethod* _optimised_method;
public:
	InjectionPoint(A* allocation, C* const_value) : _const_value(const_value),
	                                                _allocation(allocation),
	                                                _finish_points(2) {}

	C* const_value() { return _const_value; };
	A* allocation()  { return _allocation; }

	FinishPoint* add_stats(ciMethod* method, int bci) {
		// Check if not added
		for (GrowableArrayIterator<FinishPoint*> i = _finish_points.begin();
		     i != _finish_points.end();
		     ++i) {
			if ((*i)->method() == method && (*i)->bci() == bci) {
				return *i;
			}
		}

		FinishPoint* stats = new FinishPoint(method, bci);
		_finish_points.append(stats);
		return stats;
	}

	ciMethod* optimised_method() { return _optimised_method; }
	void set_optimised_method(ciMethod* optimised_method) {  _optimised_method = optimised_method; }

	void* operator new(size_t x) throw();
};

/** The point of collecting stats, encapsulates calling method and bci where a finish method is called */
template <class A, class C>
class BufferSizePredictor<A,C>::FinishPoint {
private:
	ciMethod* _method;
	int _bci;
public:
	FinishPoint(ciMethod* method, int bci) : _method(method), _bci(bci) {}

	ciMethod* method() const {
		return _method;
	};

	int bci() const {
		return _bci;
	};

	void* operator new(size_t x) throw();
};
#endif //HOTSPOT_BUFFERSIZEPREDICTOR_HPP
