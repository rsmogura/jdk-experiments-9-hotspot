#ifndef HOTSPOT_C1_BUFFERSIZEOPTO_HPP
#define HOTSPOT_C1_BUFFERSIZEOPTO_HPP

#include "c1/c1_Compilation.hpp"
#include "c1/c1_Instruction.hpp"
#include "c1/c1_ValueType.hpp"

#include "compiler/bufferSizePredictor.hpp"

class C1_BufferSizePredictor : public BufferSizePredictor<NewInstance, Constant> {
private:
		bool _has_substitutions;
		IR*  _hir;
protected:
		void profile_injection_point(InjectionPoint* point, int size_new);
public:
		C1_BufferSizePredictor() : _has_substitutions(false), _hir(NULL) {}

		void profile(IR* ir);
};
#endif //HOTSPOT_C1_BUFFERSIZEOPTO_HPP
