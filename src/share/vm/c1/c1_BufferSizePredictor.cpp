#include "c1/c1_BufferSizePredictor.hpp"
#include "c1/c1_IR.hpp"
#include "c1/c1_ValueStack.hpp"
#include "c1/c1_InstructionPrinter.hpp"
#include "compiler/compileLog.hpp"

void C1_BufferSizePredictor::profile(IR *ir) {
	_hir = ir;
	do_all_points();
	if (_has_substitutions)
		SubstitutionResolver do_subst(ir);
}


void C1_BufferSizePredictor::profile_injection_point(InjectionPoint* pt, int size_new) {
	// Now do replacement
	IntConstant* size_const = new IntConstant((jint) size_new);
	Constant* size_cosnt_instr = new Constant(size_const);

	Constant* original = pt->const_value();
	NOT_PRODUCT(size_cosnt_instr->set_printable_bci(original->printable_bci()));
	original->set_subst(size_cosnt_instr);

	InstructionStreamSubstitutionResolver(original, _hir);
	_has_substitutions = true;
	CompileLog* log = Compilation::current()->log();
	if (log != NULL) {
		log->begin_elem("In method ");
		pt->optimised_method()-> print_name(log);
		log->end_elem(" substituted buffer size %d with approximate size %d \n",
		           original->type()->as_IntConstant()->value(), size_new);
	}else {
		tty->print("In method ");
		pt->optimised_method()-> print_name(tty);
		tty->print(" substituted buffer size %d with approximate size %d \n",
		              original->type()->as_IntConstant()->value(), size_new);
	}
}

template<> void* BufferSizePredictor<NewInstance, Constant>::FinishPoint::operator new(size_t size) {
	return Compilation::current()->arena()->Amalloc_D(size);
};

template<> void* BufferSizePredictor<NewInstance, Constant>::InjectionPoint::operator new(size_t size) {
	return Compilation::current()->arena()->Amalloc_D(size);
};

template<> void* BufferSizePredictor<NewInstance, Constant>::operator new(size_t size) {
	return Compilation::current()->arena()->Amalloc_D(size);
};