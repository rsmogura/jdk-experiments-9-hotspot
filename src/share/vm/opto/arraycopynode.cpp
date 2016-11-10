/*
 * Copyright (c) 2016, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */

#include "precompiled.hpp"
#include "opto/arraycopynode.hpp"
#include "opto/graphKit.hpp"
#include "opto/escape.hpp"
#include "opto/rootnode.hpp"
#include "opto/castnode.hpp"
#include "opto/convertnode.hpp"

ArrayCopyNode::ArrayCopyNode(Compile* C, bool alloc_tightly_coupled)
  : CallNode(arraycopy_type(), NULL, TypeRawPtr::BOTTOM),
    _alloc_tightly_coupled(alloc_tightly_coupled),
    _kind(None),
    _arguments_validated(false),
    _src_type(TypeOopPtr::BOTTOM),
    _dest_type(TypeOopPtr::BOTTOM) {
  init_class_id(Class_ArrayCopy);
  init_flags(Flag_is_macro);
  C->add_macro_node(this);
}

uint ArrayCopyNode::size_of() const { return sizeof(*this); }

ArrayCopyNode* ArrayCopyNode::make(GraphKit* kit, bool may_throw,
                                   Node* src, Node* src_offset,
                                   Node* dest, Node* dest_offset,
                                   Node* length,
                                   bool alloc_tightly_coupled,
                                   Node* src_klass, Node* dest_klass,
                                   Node* src_length, Node* dest_length) {

  ArrayCopyNode* ac = new ArrayCopyNode(kit->C, alloc_tightly_coupled);
  Node* prev_mem = kit->set_predefined_input_for_runtime_call(ac);

  ac->init_req(ArrayCopyNode::Src, src);
  ac->init_req(ArrayCopyNode::SrcPos, src_offset);
  ac->init_req(ArrayCopyNode::Dest, dest);
  ac->init_req(ArrayCopyNode::DestPos, dest_offset);
  ac->init_req(ArrayCopyNode::Length, length);
  ac->init_req(ArrayCopyNode::SrcLen, src_length);
  ac->init_req(ArrayCopyNode::DestLen, dest_length);
  ac->init_req(ArrayCopyNode::SrcKlass, src_klass);
  ac->init_req(ArrayCopyNode::DestKlass, dest_klass);

  if (may_throw) {
    ac->set_req(TypeFunc::I_O , kit->i_o());
    kit->add_safepoint_edges(ac, false);
  }

  return ac;
}

void ArrayCopyNode::connect_outputs(GraphKit* kit) {
  kit->set_all_memory_call(this, true);
  kit->set_control(kit->gvn().transform(new ProjNode(this,TypeFunc::Control)));
  kit->set_i_o(kit->gvn().transform(new ProjNode(this, TypeFunc::I_O)));
  kit->make_slow_call_ex(this, kit->env()->Throwable_klass(), true);
  kit->set_all_memory_call(this);
}

#ifndef PRODUCT
const char* ArrayCopyNode::_kind_names[] = {"arraycopy", "arraycopy, validated arguments", "clone", "oop array clone", "CopyOf", "CopyOfRange"};

void ArrayCopyNode::dump_spec(outputStream *st) const {
  CallNode::dump_spec(st);
  st->print(" (%s%s)", _kind_names[_kind], _alloc_tightly_coupled ? ", tightly coupled allocation" : "");
}

void ArrayCopyNode::dump_compact_spec(outputStream* st) const {
  st->print("%s%s", _kind_names[_kind], _alloc_tightly_coupled ? ",tight" : "");
}
#endif

intptr_t ArrayCopyNode::get_length_if_constant(PhaseGVN *phase) const {
  // check that length is constant
  Node* length = in(ArrayCopyNode::Length);
  const Type* length_type = phase->type(length);

  if (length_type == Type::TOP) {
    return -1;
  }

  assert(is_clonebasic() || is_arraycopy() || is_copyof() || is_copyofrange(), "unexpected array copy type");

  return is_clonebasic() ? length->find_intptr_t_con(-1) : length->find_int_con(-1);
}

int ArrayCopyNode::get_count(PhaseGVN *phase) const {
  Node* src = in(ArrayCopyNode::Src);
  const Type* src_type = phase->type(src);

  if (is_clonebasic()) {
    if (src_type->isa_instptr()) {
      const TypeInstPtr* inst_src = src_type->is_instptr();
      ciInstanceKlass* ik = inst_src->klass()->as_instance_klass();
      // ciInstanceKlass::nof_nonstatic_fields() doesn't take injected
      // fields into account. They are rare anyway so easier to simply
      // skip instances with injected fields.
      if ((!inst_src->klass_is_exact() && (ik->is_interface() || ik->has_subklass())) || ik->has_injected_fields()) {
        return -1;
      }
      int nb_fields = ik->nof_nonstatic_fields();
      return nb_fields;
    } else {
      const TypeAryPtr* ary_src = src_type->isa_aryptr();
      assert (ary_src != NULL, "not an array or instance?");
      // clone passes a length as a rounded number of longs. If we're
      // cloning an array we'll do it element by element. If the
      // length input to ArrayCopyNode is constant, length of input
      // array must be too.

      assert((get_length_if_constant(phase) == -1) == !ary_src->size()->is_con() ||
             phase->is_IterGVN(), "inconsistent");

      if (ary_src->size()->is_con()) {
        return ary_src->size()->get_con();
      }
      return -1;
    }
  }

  return get_length_if_constant(phase);
}

Node* ArrayCopyNode::try_clone_instance(PhaseGVN *phase, bool can_reshape, int count) {
  if (!is_clonebasic()) {
    return NULL;
  }

  Node* src = in(ArrayCopyNode::Src);
  Node* dest = in(ArrayCopyNode::Dest);
  Node* ctl = in(TypeFunc::Control);
  Node* in_mem = in(TypeFunc::Memory);

  const Type* src_type = phase->type(src);

  assert(src->is_AddP(), "should be base + off");
  assert(dest->is_AddP(), "should be base + off");
  Node* base_src = src->in(AddPNode::Base);
  Node* base_dest = dest->in(AddPNode::Base);

  MergeMemNode* mem = MergeMemNode::make(in_mem);

  const TypeInstPtr* inst_src = src_type->isa_instptr();

  if (inst_src == NULL) {
    return NULL;
  }

  if (!inst_src->klass_is_exact()) {
    ciInstanceKlass* ik = inst_src->klass()->as_instance_klass();
    assert(!ik->is_interface() && !ik->has_subklass(), "inconsistent klass hierarchy");
    phase->C->dependencies()->assert_leaf_type(ik);
  }

  ciInstanceKlass* ik = inst_src->klass()->as_instance_klass();
  assert(ik->nof_nonstatic_fields() <= ArrayCopyLoadStoreMaxElem, "too many fields");

  for (int i = 0; i < count; i++) {
    ciField* field = ik->nonstatic_field_at(i);
    int fieldidx = phase->C->alias_type(field)->index();
    const TypePtr* adr_type = phase->C->alias_type(field)->adr_type();
    Node* off = phase->MakeConX(field->offset());
    Node* next_src = phase->transform(new AddPNode(base_src,base_src,off));
    Node* next_dest = phase->transform(new AddPNode(base_dest,base_dest,off));
    BasicType bt = field->layout_type();

    const Type *type;
    if (bt == T_OBJECT) {
      if (!field->type()->is_loaded()) {
        type = TypeInstPtr::BOTTOM;
      } else {
        ciType* field_klass = field->type();
        type = TypeOopPtr::make_from_klass(field_klass->as_klass());
      }
    } else {
      type = Type::get_const_basic_type(bt);
    }

    Node* v = LoadNode::make(*phase, ctl, mem->memory_at(fieldidx), next_src, adr_type, type, bt, MemNode::unordered);
    v = phase->transform(v);
    Node* s = StoreNode::make(*phase, ctl, mem->memory_at(fieldidx), next_dest, adr_type, v, bt, MemNode::unordered);
    s = phase->transform(s);
    mem->set_memory_at(fieldidx, s);
  }

  if (!finish_transform(phase, can_reshape, ctl, mem)) {
    // Return NodeSentinel to indicate that the transform failed
    return NodeSentinel;
  }

  return mem;
}

bool ArrayCopyNode::prepare_array_copy(PhaseGVN *phase, bool can_reshape,
                                       Node*& adr_src,
                                       Node*& base_src,
                                       Node*& adr_dest,
                                       Node*& base_dest,
                                       BasicType& copy_type,
                                       const Type*& value_type,
                                       bool& disjoint_bases) {
  Node* src = in(ArrayCopyNode::Src);
  Node* dest = in(ArrayCopyNode::Dest);
  const Type* src_type = phase->type(src);
  const TypeAryPtr* ary_src = src_type->isa_aryptr();
  assert(ary_src != NULL, "should be an array copy/clone");

  if (is_arraycopy() || is_copyofrange() || is_copyof()) {
    const Type* dest_type = phase->type(dest);
    const TypeAryPtr* ary_dest = dest_type->isa_aryptr();
    Node* src_offset = in(ArrayCopyNode::SrcPos);
    Node* dest_offset = in(ArrayCopyNode::DestPos);

    // newly allocated object is guaranteed to not overlap with source object
    disjoint_bases = is_alloc_tightly_coupled();

    if (ary_src  == NULL || ary_src->klass()  == NULL ||
        ary_dest == NULL || ary_dest->klass() == NULL) {
      // We don't know if arguments are arrays
      return false;
    }

    BasicType src_elem  = ary_src->klass()->as_array_klass()->element_type()->basic_type();
    BasicType dest_elem = ary_dest->klass()->as_array_klass()->element_type()->basic_type();
    if (src_elem  == T_ARRAY)  src_elem  = T_OBJECT;
    if (dest_elem == T_ARRAY)  dest_elem = T_OBJECT;

    if (src_elem != dest_elem || dest_elem == T_VOID) {
      // We don't know if arguments are arrays of the same type
      return false;
    }

    if (dest_elem == T_OBJECT && (!is_alloc_tightly_coupled() || !GraphKit::use_ReduceInitialCardMarks())) {
      // It's an object array copy but we can't emit the card marking
      // that is needed
      return false;
    }

    value_type = ary_src->elem();

    base_src = src;
    base_dest = dest;

    uint shift  = exact_log2(type2aelembytes(dest_elem));
    uint header = arrayOopDesc::base_offset_in_bytes(dest_elem);

    adr_src = src;
    adr_dest = dest;

    src_offset = Compile::conv_I2X_index(phase, src_offset, ary_src->size());
    dest_offset = Compile::conv_I2X_index(phase, dest_offset, ary_dest->size());

    Node* src_scale = phase->transform(new LShiftXNode(src_offset, phase->intcon(shift)));
    Node* dest_scale = phase->transform(new LShiftXNode(dest_offset, phase->intcon(shift)));

    adr_src = phase->transform(new AddPNode(base_src, adr_src, src_scale));
    adr_dest = phase->transform(new AddPNode(base_dest, adr_dest, dest_scale));

    adr_src = new AddPNode(base_src, adr_src, phase->MakeConX(header));
    adr_dest = new AddPNode(base_dest, adr_dest, phase->MakeConX(header));

    adr_src = phase->transform(adr_src);
    adr_dest = phase->transform(adr_dest);

    copy_type = dest_elem;
  } else {
    assert (is_clonebasic(), "should be");

    disjoint_bases = true;
    assert(src->is_AddP(), "should be base + off");
    assert(dest->is_AddP(), "should be base + off");
    adr_src = src;
    base_src = src->in(AddPNode::Base);
    adr_dest = dest;
    base_dest = dest->in(AddPNode::Base);

    assert(phase->type(src->in(AddPNode::Offset))->is_intptr_t()->get_con() == phase->type(dest->in(AddPNode::Offset))->is_intptr_t()->get_con(), "same start offset?");
    BasicType elem = ary_src->klass()->as_array_klass()->element_type()->basic_type();
    if (elem == T_ARRAY)  elem = T_OBJECT;

    int diff = arrayOopDesc::base_offset_in_bytes(elem) - phase->type(src->in(AddPNode::Offset))->is_intptr_t()->get_con();
    assert(diff >= 0, "clone should not start after 1st array element");
    if (diff > 0) {
      adr_src = phase->transform(new AddPNode(base_src, adr_src, phase->MakeConX(diff)));
      adr_dest = phase->transform(new AddPNode(base_dest, adr_dest, phase->MakeConX(diff)));
    }

    copy_type = elem;
    value_type = ary_src->elem();
  }
  return true;
}

const TypePtr* ArrayCopyNode::get_address_type(PhaseGVN *phase, Node* n) {
  const Type* at = phase->type(n);
  assert(at != Type::TOP, "unexpected type");
  const TypePtr* atp = at->isa_ptr();
  // adjust atp to be the correct array element address type
  atp = atp->add_offset(Type::OffsetBot);
  return atp;
}

void ArrayCopyNode::array_copy_test_overlap(PhaseGVN *phase, bool can_reshape, bool disjoint_bases, int count, Node*& forward_ctl, Node*& backward_ctl) {
  Node* ctl = in(TypeFunc::Control);
  if (!disjoint_bases && count > 1) {
    Node* src_offset = in(ArrayCopyNode::SrcPos);
    Node* dest_offset = in(ArrayCopyNode::DestPos);
    assert(src_offset != NULL && dest_offset != NULL, "should be");
    Node* cmp = phase->transform(new CmpINode(src_offset, dest_offset));
    Node *bol = phase->transform(new BoolNode(cmp, BoolTest::lt));
    IfNode *iff = new IfNode(ctl, bol, PROB_FAIR, COUNT_UNKNOWN);

    phase->transform(iff);

    forward_ctl = phase->transform(new IfFalseNode(iff));
    backward_ctl = phase->transform(new IfTrueNode(iff));
  } else {
    forward_ctl = ctl;
  }
}

Node* ArrayCopyNode::array_copy_forward(PhaseGVN *phase,
                                        bool can_reshape,
                                        Node* forward_ctl,
                                        Node* start_mem_src,
                                        Node* start_mem_dest,
                                        const TypePtr* atp_src,
                                        const TypePtr* atp_dest,
                                        Node* adr_src,
                                        Node* base_src,
                                        Node* adr_dest,
                                        Node* base_dest,
                                        BasicType copy_type,
                                        const Type* value_type,
                                        int count) {
  Node* mem = phase->C->top();
  if (!forward_ctl->is_top()) {
    // copy forward
    mem = start_mem_dest;

    if (count > 0) {
      Node* v = LoadNode::make(*phase, forward_ctl, start_mem_src, adr_src, atp_src, value_type, copy_type, MemNode::unordered);
      v = phase->transform(v);
      mem = StoreNode::make(*phase, forward_ctl, mem, adr_dest, atp_dest, v, copy_type, MemNode::unordered);
      mem = phase->transform(mem);
      for (int i = 1; i < count; i++) {
        Node* off  = phase->MakeConX(type2aelembytes(copy_type) * i);
        Node* next_src = phase->transform(new AddPNode(base_src,adr_src,off));
        Node* next_dest = phase->transform(new AddPNode(base_dest,adr_dest,off));
        v = LoadNode::make(*phase, forward_ctl, mem, next_src, atp_src, value_type, copy_type, MemNode::unordered);
        v = phase->transform(v);
        mem = StoreNode::make(*phase, forward_ctl,mem,next_dest,atp_dest,v, copy_type, MemNode::unordered);
        mem = phase->transform(mem);
      }
    } else if(can_reshape) {
      PhaseIterGVN* igvn = phase->is_IterGVN();
      igvn->_worklist.push(adr_src);
      igvn->_worklist.push(adr_dest);
    }
  }
  return mem;
}

Node* ArrayCopyNode::array_copy_backward(PhaseGVN *phase,
                                         bool can_reshape,
                                         Node* backward_ctl,
                                         Node* start_mem_src,
                                         Node* start_mem_dest,
                                         const TypePtr* atp_src,
                                         const TypePtr* atp_dest,
                                         Node* adr_src,
                                         Node* base_src,
                                         Node* adr_dest,
                                         Node* base_dest,
                                         BasicType copy_type,
                                         const Type* value_type,
                                         int count) {
  Node* mem = phase->C->top();
  if (!backward_ctl->is_top()) {
    // copy backward
    mem = start_mem_dest;

    if (count > 0) {
      for (int i = count-1; i >= 1; i--) {
        Node* off  = phase->MakeConX(type2aelembytes(copy_type) * i);
        Node* next_src = phase->transform(new AddPNode(base_src,adr_src,off));
        Node* next_dest = phase->transform(new AddPNode(base_dest,adr_dest,off));
        Node* v = LoadNode::make(*phase, backward_ctl, mem, next_src, atp_src, value_type, copy_type, MemNode::unordered);
        v = phase->transform(v);
        mem = StoreNode::make(*phase, backward_ctl,mem,next_dest,atp_dest,v, copy_type, MemNode::unordered);
        mem = phase->transform(mem);
      }
      Node* v = LoadNode::make(*phase, backward_ctl, mem, adr_src, atp_src, value_type, copy_type, MemNode::unordered);
      v = phase->transform(v);
      mem = StoreNode::make(*phase, backward_ctl, mem, adr_dest, atp_dest, v, copy_type, MemNode::unordered);
      mem = phase->transform(mem);
    } else if(can_reshape) {
      PhaseIterGVN* igvn = phase->is_IterGVN();
      igvn->_worklist.push(adr_src);
      igvn->_worklist.push(adr_dest);
    }
  }
  return mem;
}

bool ArrayCopyNode::finish_transform(PhaseGVN *phase, bool can_reshape,
                                     Node* ctl, Node *mem) {
  if (can_reshape) {
    PhaseIterGVN* igvn = phase->is_IterGVN();
    igvn->set_delay_transform(false);
    if (is_clonebasic()) {
      Node* out_mem = proj_out(TypeFunc::Memory);

      if (out_mem->outcnt() != 1 || !out_mem->raw_out(0)->is_MergeMem() ||
          out_mem->raw_out(0)->outcnt() != 1 || !out_mem->raw_out(0)->raw_out(0)->is_MemBar()) {
        assert(!GraphKit::use_ReduceInitialCardMarks(), "can only happen with card marking");
        return false;
      }

      igvn->replace_node(out_mem->raw_out(0), mem);

      Node* out_ctl = proj_out(TypeFunc::Control);
      igvn->replace_node(out_ctl, ctl);
    } else {
      // replace fallthrough projections of the ArrayCopyNode by the
      // new memory, control and the input IO.
      CallProjections callprojs;
      extract_projections(&callprojs, true, false);

      if (callprojs.fallthrough_ioproj != NULL) {
        igvn->replace_node(callprojs.fallthrough_ioproj, in(TypeFunc::I_O));
      }
      if (callprojs.fallthrough_memproj != NULL) {
        igvn->replace_node(callprojs.fallthrough_memproj, mem);
      }
      if (callprojs.fallthrough_catchproj != NULL) {
        igvn->replace_node(callprojs.fallthrough_catchproj, ctl);
      }

      // The ArrayCopyNode is not disconnected. It still has the
      // projections for the exception case. Replace current
      // ArrayCopyNode with a dummy new one with a top() control so
      // that this part of the graph stays consistent but is
      // eventually removed.

      set_req(0, phase->C->top());
      remove_dead_region(phase, can_reshape);
    }
  } else {
    if (in(TypeFunc::Control) != ctl) {
      // we can't return new memory and control from Ideal at parse time
      assert(!is_clonebasic(), "added control for clone?");
      return false;
    }
  }
  return true;
}


Node *ArrayCopyNode::Ideal(PhaseGVN *phase, bool can_reshape) {
  if (remove_dead_region(phase, can_reshape))  return this;

  if (StressArrayCopyMacroNode && !can_reshape) {
    phase->record_for_igvn(this);
    return NULL;
  }

  // See if it's a small array copy and we can inline it as
  // loads/stores
  // Here we can only do:
  // - arraycopy if all arguments were validated before and we don't
  // need card marking
  // - clone for which we don't need to do card marking

  if (!is_clonebasic() && !is_arraycopy_validated() &&
      !is_copyofrange_validated() && !is_copyof_validated()) {
    return NULL;
  }

  assert(in(TypeFunc::Control) != NULL &&
         in(TypeFunc::Memory) != NULL &&
         in(ArrayCopyNode::Src) != NULL &&
         in(ArrayCopyNode::Dest) != NULL &&
         in(ArrayCopyNode::Length) != NULL &&
         ((in(ArrayCopyNode::SrcPos) != NULL && in(ArrayCopyNode::DestPos) != NULL) ||
          is_clonebasic()), "broken inputs");

  if (in(TypeFunc::Control)->is_top() ||
      in(TypeFunc::Memory)->is_top() ||
      phase->type(in(ArrayCopyNode::Src)) == Type::TOP ||
      phase->type(in(ArrayCopyNode::Dest)) == Type::TOP ||
      (in(ArrayCopyNode::SrcPos) != NULL && in(ArrayCopyNode::SrcPos)->is_top()) ||
      (in(ArrayCopyNode::DestPos) != NULL && in(ArrayCopyNode::DestPos)->is_top())) {
    return NULL;
  }

  int count = get_count(phase);

  if (count < 0 || count > ArrayCopyLoadStoreMaxElem) {
    return NULL;
  }

  Node* mem = try_clone_instance(phase, can_reshape, count);
  if (mem != NULL) {
    return (mem == NodeSentinel) ? NULL : mem;
  }

  Node* adr_src = NULL;
  Node* base_src = NULL;
  Node* adr_dest = NULL;
  Node* base_dest = NULL;
  BasicType copy_type = T_ILLEGAL;
  const Type* value_type = NULL;
  bool disjoint_bases = false;

  if (!prepare_array_copy(phase, can_reshape,
                          adr_src, base_src, adr_dest, base_dest,
                          copy_type, value_type, disjoint_bases)) {
    return NULL;
  }

  Node* src = in(ArrayCopyNode::Src);
  Node* dest = in(ArrayCopyNode::Dest);
  const TypePtr* atp_src = get_address_type(phase, src);
  const TypePtr* atp_dest = get_address_type(phase, dest);
  uint alias_idx_src = phase->C->get_alias_index(atp_src);
  uint alias_idx_dest = phase->C->get_alias_index(atp_dest);

  Node *in_mem = in(TypeFunc::Memory);
  Node *start_mem_src = in_mem;
  Node *start_mem_dest = in_mem;
  if (in_mem->is_MergeMem()) {
    start_mem_src = in_mem->as_MergeMem()->memory_at(alias_idx_src);
    start_mem_dest = in_mem->as_MergeMem()->memory_at(alias_idx_dest);
  }


  if (can_reshape) {
    assert(!phase->is_IterGVN()->delay_transform(), "cannot delay transforms");
    phase->is_IterGVN()->set_delay_transform(true);
  }

  Node* backward_ctl = phase->C->top();
  Node* forward_ctl = phase->C->top();
  array_copy_test_overlap(phase, can_reshape, disjoint_bases, count, forward_ctl, backward_ctl);

  Node* forward_mem = array_copy_forward(phase, can_reshape, forward_ctl,
                                         start_mem_src, start_mem_dest,
                                         atp_src, atp_dest,
                                         adr_src, base_src, adr_dest, base_dest,
                                         copy_type, value_type, count);

  Node* backward_mem = array_copy_backward(phase, can_reshape, backward_ctl,
                                           start_mem_src, start_mem_dest,
                                           atp_src, atp_dest,
                                           adr_src, base_src, adr_dest, base_dest,
                                           copy_type, value_type, count);

  Node* ctl = NULL;
  if (!forward_ctl->is_top() && !backward_ctl->is_top()) {
    ctl = new RegionNode(3);
    mem = new PhiNode(ctl, Type::MEMORY, atp_dest);
    ctl->init_req(1, forward_ctl);
    mem->init_req(1, forward_mem);
    ctl->init_req(2, backward_ctl);
    mem->init_req(2, backward_mem);
    ctl = phase->transform(ctl);
    mem = phase->transform(mem);
  } else if (!forward_ctl->is_top()) {
    ctl = forward_ctl;
    mem = forward_mem;
  } else {
    assert(!backward_ctl->is_top(), "no copy?");
    ctl = backward_ctl;
    mem = backward_mem;
  }

  if (can_reshape) {
    assert(phase->is_IterGVN()->delay_transform(), "should be delaying transforms");
    phase->is_IterGVN()->set_delay_transform(false);
  }

  MergeMemNode* out_mem = MergeMemNode::make(in_mem);
  out_mem->set_memory_at(alias_idx_dest, mem);
  mem = out_mem;

  if (!finish_transform(phase, can_reshape, ctl, mem)) {
    return NULL;
  }

  return mem;
}

bool ArrayCopyNode::may_modify(const TypeOopPtr *t_oop, PhaseTransform *phase) {
  Node* dest = in(ArrayCopyNode::Dest);
  if (dest->is_top()) {
    return false;
  }
  const TypeOopPtr* dest_t = phase->type(dest)->is_oopptr();
  assert(!dest_t->is_known_instance() || _dest_type->is_known_instance(), "result of EA not recorded");
  assert(in(ArrayCopyNode::Src)->is_top() || !phase->type(in(ArrayCopyNode::Src))->is_oopptr()->is_known_instance() ||
         _src_type->is_known_instance(), "result of EA not recorded");

  if (_dest_type != TypeOopPtr::BOTTOM || t_oop->is_known_instance()) {
    assert(_dest_type == TypeOopPtr::BOTTOM || _dest_type->is_known_instance(), "result of EA is known instance");
    return t_oop->instance_id() == _dest_type->instance_id();
  }

  return CallNode::may_modify_arraycopy_helper(dest_t, t_oop, phase);
}

bool ArrayCopyNode::may_modify_helper(const TypeOopPtr *t_oop, Node* n, PhaseTransform *phase, ArrayCopyNode*& ac) {
  if (n->Opcode() == Op_StoreCM ||
      n->Opcode() == Op_StoreB) {
    // Ignore card mark stores
    n = n->in(MemNode::Memory);
  }

  if (n->is_Proj()) {
    n = n->in(0);
    if (n->is_Call() && n->as_Call()->may_modify(t_oop, phase)) {
      if (n->isa_ArrayCopy() != NULL) {
        ac = n->as_ArrayCopy();
      }
      return true;
    }
  }
  return false;
}

bool ArrayCopyNode::may_modify(const TypeOopPtr *t_oop, MemBarNode* mb, PhaseTransform *phase, ArrayCopyNode*& ac) {
  Node* mem = mb->in(TypeFunc::Memory);

  if (mem->is_MergeMem()) {
    Node* n = mem->as_MergeMem()->memory_at(Compile::AliasIdxRaw);
    if (may_modify_helper(t_oop, n, phase, ac)) {
      return true;
    } else if (n->is_Phi()) {
      for (uint i = 1; i < n->req(); i++) {
        if (n->in(i) != NULL) {
          if (may_modify_helper(t_oop, n->in(i), phase, ac)) {
            return true;
          }
        }
      }
    }
  }

  return false;
}

// Does this array copy modify offsets between offset_lo and offset_hi
// in the destination array
// if must_modify is false, return true if the copy could write
// between offset_lo and offset_hi
// if must_modify is true, return true if the copy is guaranteed to
// write between offset_lo and offset_hi
bool ArrayCopyNode::modifies(intptr_t offset_lo, intptr_t offset_hi, PhaseTransform* phase, bool must_modify) {
  assert(_kind == ArrayCopy || _kind == CopyOf || _kind == CopyOfRange, "only for real array copies");

  Node* dest = in(ArrayCopyNode::Dest);
  Node* src_pos = in(ArrayCopyNode::SrcPos);
  Node* dest_pos = in(ArrayCopyNode::DestPos);
  Node* len = in(ArrayCopyNode::Length);

  const TypeInt *dest_pos_t = phase->type(dest_pos)->isa_int();
  const TypeInt *len_t = phase->type(len)->isa_int();
  const TypeAryPtr* ary_t = phase->type(dest)->isa_aryptr();

  if (dest_pos_t != NULL && len_t != NULL && ary_t != NULL) {
    BasicType ary_elem = ary_t->klass()->as_array_klass()->element_type()->basic_type();
    uint header = arrayOopDesc::base_offset_in_bytes(ary_elem);
    uint elemsize = type2aelembytes(ary_elem);

    jlong dest_pos_plus_len_lo = (((jlong)dest_pos_t->_lo) + len_t->_lo) * elemsize + header;
    jlong dest_pos_plus_len_hi = (((jlong)dest_pos_t->_hi) + len_t->_hi) * elemsize + header;
    jlong dest_pos_lo = ((jlong)dest_pos_t->_lo) * elemsize + header;
    jlong dest_pos_hi = ((jlong)dest_pos_t->_hi) * elemsize + header;

    if (must_modify) {
      if (offset_lo >= dest_pos_hi && offset_hi < dest_pos_plus_len_lo) {
        return true;
      }
    } else {
      if (offset_hi >= dest_pos_lo && offset_lo < dest_pos_plus_len_hi) {
        return true;
      }
    }
  }
  return false;
}

bool ArrayCopyNode::Ideal_ArrayCopy(ArrayCopyNode* ac, Node*& input_ctrl, CatchProjNode*& out_control, ProjNode*& out_memory, ProjNode*& out_io) {
  assert(ac, "");
	input_ctrl = NULL;
	out_control = NULL;
	out_memory = out_io = NULL;
	int out_ctrls = 0, out_mems = 0, out_ios = 0;

	input_ctrl = ac->in(TypeFunc::Control);
	if (!input_ctrl)
		return false;

	// Iterate over output edges to find
  for (DUIterator i = ac->outs(); ac->has_out(i); i++) {
    ProjNode* proj = ac->out(i)->isa_Proj();
	  Node* out; // Helper

    if (!proj)
      continue;

    if (proj->_con == TypeFunc::Control) {
	    out = proj->unique_out_or_null();
	    if (!out || !out->is_Catch())
		    return false;
	    CatchNode* catch_node = out->as_Catch();

      // Go trough all catch projections to extract fall through control
	    for (DUIterator_Fast imax, i = catch_node->fast_outs(imax); i < imax; i++) {
        CatchProjNode* catch_proj = catch_node->fast_out(i)->isa_CatchProj();
        if (!catch_proj) {
          assert(catch_proj, "Should be catch");
          return false;
        }
        if (catch_proj->_con == CatchProjNode::fall_through_index) {
          out_control = catch_proj;
	        out_ctrls++;
        }
      }
    }else if (proj->_con == TypeFunc::Memory && !proj->_is_io_use){
      out_memory = proj;
	    out_mems++;
    }else if (proj->_con == TypeFunc::I_O && !proj->_is_io_use){
	    out_io = proj;
	    out_ios++;
    }
  }

	// Check how many controls has been found, it should be 1 for ideal copy
	if (out_ctrls == 1 && out_mems == 1 && out_ios == 1) {
		return true;
	}else {
		debug_only(input_ctrl = NULL; out_control = NULL; out_memory = out_io = NULL;);
		return false;
	}
}

void EliminateArrayCopyPhase::eliminate_all_array_copy() {

  for (int i=0; i < C->macro_count(); i++) {
    ArrayCopyNode* arrcpy = C->macro_node(i)->isa_ArrayCopy();
    if (arrcpy)
      eliminate_single_array_copy(arrcpy);
  }
}

void EliminateArrayCopyPhase::set_src_length_with_membar(Node* len, Node* &current_control, Node* &current_mem) {
	// And finish changes by setting new array length
	set_array_length(arrcpy->in(ArrayCopyNode::Src), len, current_control, current_mem);

	// Src can escape (if dst was escaping) new size has to be visible by other threads
	// Doesn't need to care about concurrent scan, as it will just see previous array,
	// and dummy array is not referenced anywhere
	if (!C->congraph()->not_global_escape(arrcpy->in(ArrayCopyNode::Dest)))
		insert_mem_bar(&current_control, &current_mem, Op_MemBarRelease);
}

bool EliminateArrayCopyPhase::eliminate_single_array_copy(ArrayCopyNode *arrcpy) {
	this->arrcpy = arrcpy;

  Node* src = arrcpy->in(ArrayCopyNode::Src);
  Node* dst = arrcpy->in(ArrayCopyNode::Dest);
  Node* src_pos = arrcpy->in(ArrayCopyNode::SrcPos);
  Node* dst_pos = arrcpy->in(ArrayCopyNode::DestPos);
	Node* src_len = arrcpy->in(ArrayCopyNode::SrcLen);
	Node* dst_len = arrcpy->in(ArrayCopyNode::DestLen);

  TypeNode* src_klass = arrcpy->in(ArrayCopyNode::SrcKlass)->as_Type();
  TypeNode* dst_klass = arrcpy->in(ArrayCopyNode::DestKlass)->as_Type();

  // Faster debug trap
  const char* n = arrcpy->jvms()->method()->name()->as_utf8();
  if (strcmp(C->method()->name()->as_utf8(), "sayHello4") == 0
      || strcmp(C->method()->name()->as_utf8(), "start") == 0) {
    arrcpy->jvms();
  }
	// No dest use before copy - this can be relaxed to check if array escapes
	// in call before copy, modifications are, in theory, allowed as later we check if
	// array copy length is same as dest length, so it would be overwritten in any awy
	if (false || !arrcpy->is_alloc_tightly_coupled())
		return false;

  // Array must not escape
  if (!C->congraph() || !C->congraph()
          ->not_global_escape(src))
    return false;

  // Src and dest offsets have to be zero
  if (_igvn.find_int_con(src_pos, -1) != 0 || _igvn.find_int_con(dst_pos, -1) != 0)
    return false;

  // Check source and destination klass
  if ( !(src_klass->type()->isa_klassptr() &&
			   dst_klass->type()->isa_klassptr() &&
			   src_klass->type()->is_klassptr()->klass()->is_array_klass() &&
			   dst_klass->type()->is_klassptr()->klass()->is_array_klass()) )
	  //TODO Should handle be used to prevent unloading?
    return false;

  BasicType element_type = T_CONFLICT;
  {
    // Elements types should be primitive and same
    ciArrayKlass *src_arr_klass = src_klass->type()->is_klassptr()->klass()->as_array_klass();
    ciArrayKlass *dst_arr_klass = dst_klass->type()->is_klassptr()->klass()->as_array_klass();
    element_type = src_arr_klass->base_element_type()->basic_type();

	  // Element types must be same
    if (!(element_type <= T_LONG && element_type == dst_arr_klass->base_element_type()->basic_type()))
      return false;
  }

  // Would be true on many platforms, this implies (see later comment) that object alignment is multiplication
	// of element size. Returns false for long[] on ancient 32 bit platforms.
	const int element_sz_byte = type2aelembytes(element_type);
  if (element_sz_byte > ObjectAlignmentInBytes)
    return false;
	assert(element_sz_byte < HeapWordSize && is_power_of_2(element_sz_byte) && is_power_of_2(ObjectAlignmentInBytes),
	       "Right now should be");

  Node* copy_len = arrcpy->in(ArrayCopyNode::Length);
  AllocateArrayNode* dst_alloc = AllocateArrayNode::Ideal_array_allocation(dst, &_igvn);

	AllocateArrayNode* allocateArrayNode = AllocateArrayNode::Ideal_array_allocation(dst, &_igvn);
	if (!allocateArrayNode)
		return false;

  // Check if lengths matches - right now conseravtively, later can check if there is such a possibility
  // and add run-time checks
  //if ( !dst_alloc || dst_alloc->in(AllocateNode::ALength) != len )
  //  return false;

  // Extract Ideal allocation nodes
  Node*          cpy_in_ctrl; // Not used
  CatchProjNode* out_ctrl;
  ProjNode*      out_mem;
	ProjNode*      out_io;

  if (!ArrayCopyNode::Ideal_ArrayCopy(arrcpy, cpy_in_ctrl, out_ctrl, out_mem, out_io))
    return false;

  GrowableArray<Node*> src_roots;
  GrowableArray<Node*> usages;
  Node_List helper_list;

  if (!collect_array_allocations(src, src_roots))
    return false;

  // Collect roots, there can be more then one, in case of allocate bigger array, append loops
  for (int j=0; j < src_roots.length(); j++) {
    if (src_roots.at(j)->as_AllocateArray()->_is_scalar_replaceable)
      return false;
  }

	// Collect array usages stopping at this array copy
	helper.clear();
	helper.append(arrcpy);
	helper.append(allocateArrayNode);
	helper.append(allocateArrayNode->initialization());

  if (!collect_array_usages(src_roots, helper, usages))
      return false;

  // Check if usages are NOT after array copy
  for (int i=0; i < usages.length(); i++) {
    Node* use = usages.at(i);
		// Check if any array usage can get control from this arrcpy
	  // If yes this means that if src <- dest (no copy), and dest is read
	  // or modified then read of src can get, set modified content
	  // This check includes ass well all arg stack and local arguments
	  helper.clear();
	  if (use != arrcpy && find_parent_skip_alloc(use, arrcpy->_idx, src_roots, helper)) {
		  tty->print("ArrayCopyElimination: FAIL: Node reaches array copy: ");
		  use->dump_comp();
		  return false;
	  }
		debug_only(assert_reaches_root(use, dst));
  }

	if (!arrcpy->is_alloc_tightly_coupled()) {
		// Should check if array escapes to make more generic
		return false;
	}

  if (!dst->is_CheckCastPP()) {
    assert(false, "Should be CheckCastPP for tightly coupled allocations");
    return false;
  }

	tty->print("ArrayCopyElimination: SUCCESS: Graph valid, performing reshaping at ");
	arrcpy->dump();

	// Perform actual reshaping, now there is no point back

	// Update src escape state so later expansions will insert proper barriers
	for (int i=0; i < src_roots.length(); i++)
		src_roots.at(i)->as_AllocateArray()->_is_non_escaping = allocateArrayNode->_is_non_escaping;

  // If len is visible at allocation, it's passed as stack, and probably we can eliminate allocation, too.
	// Can we?
	// TODO Check this approach later

	this->eliminated = arrcpy;

	Node *start_ctl, *start_mem;
	start_ctl = eliminated->in(TypeFunc::Control);
	start_mem = eliminated->in(TypeFunc::Memory);

	// Separate eliminated node(s)
	separate_eliminated_nodes(out_ctrl, out_mem, out_io);

	// Local variables to track control and mem
	Node* current_control;
	Node* current_mem     = start_mem;

	// Insert first check if copy len == dest len, it's not always true, see Arrays.copyOf and min
	// inside to get real-life example
	{
		assert(dst_len->bottom_type()->basic_type() == T_INT && copy_len->bottom_type()->basic_type() == T_INT,
		       "Should be ints");
		Node     *same_lenghts_cmp   = transform_later(new CmpINode(dst_len, copy_len));
		BoolNode *same_lenshts_bool  = transform_later(new BoolNode(same_lenghts_cmp, BoolTest::eq));
		Node *yes, *no;
		make_if(start_ctl, same_lenshts_bool, yes, no);
		slow_path->set_req(RegionNode::Control + 0, no);
		current_control = yes;
	}

	// Check if src array can be truncated, there are three cases:
	//
	// (1) copy_length and src_length are same          -> pass array
	// (2) src_length - copy_length >= object alignment -> change source length, as 'truncated' src still
	//                                                  -> fits into heap object alignment
	// (3) src is big enough to hold new array header   -> install new header, so GC is happy
	//                                                     and truncate src
	//
	// There is one more possible case, to insert empty Object(), but let's skip this corner
	// case, right now.
	//
	// (2) & (1) is folded into one case, as aligning src_len and cpy_len handles boths
	// and calculations of (2) & (1) can be input to (3)
	//
	// Evaluation is performed on 64bit integers, so there is no possibility of overflow
	//
	// We assumed element size is less than min object alignment, and min object alignment
	// is greater or equal HeapWordSize. All have to be power of 2.
	// Array header is HeapWordSize aligned, so array header is multiplication of element size,
	// same "object alignment". Source is by default aligned, so everything can be expressed
	// in terms of array elements.
	//
	// And below calculations are correct, and we can divide (or shift for performance reasons)
	// Really? Studies were long time ago... and it was math...
	//
	// Additionally, we are in if dst len == copy len, and probably one of it is compile time const
	// so optimiser can do nice constant folding.

	int   element_sz_log        = exact_log2(element_sz_byte);
	Node* element_sz_log_node_i = transform_later(ConINode::make(element_sz_log));
	Node* element_sz_log_node_l = transform_later(ConLNode::make(element_sz_log));

	Node* elements_per_align    = transform_later(new RShiftLNode(
          transform_later(ConLNode::make(ObjectAlignmentInBytes)), element_sz_log_node_i));
	Node* elements_per_header   = transform_later(new RShiftLNode(
          transform_later(ConLNode::make(arrayOopDesc::base_offset_in_bytes(element_type))), element_sz_log_node_i));

	Node* src_len_aligned = alignx_up_log(transform_later(new ConvI2LNode(src_len)),  elements_per_align);
	Node* tail_start      = alignx_up_log(transform_later(new ConvI2LNode(copy_len)), elements_per_align);

	int final_slot = RegionNode::Control + 1; // First slots occupied by slow path

	// case (2) & (1) - if src_len_aligned - tail_start == 0, both arrays ends
	// at same "aligned" heap object, so free to set new lenght
	{
		Node *same_align_cmp      = transform_later(new CmpLNode(src_len_aligned, tail_start));
		BoolNode *same_align_bool = transform_later(new BoolNode(same_align_cmp, BoolTest::eq))->as_Bool();
		Node *yes, *no;
		make_if(current_control, same_align_bool, yes, no);

		// Not same, right now move back
		slow_path->set_req(RegionNode::Control + 1, no);

		// Same, update length, and connect final outputs
		current_control = yes;
		set_src_length_with_membar(copy_len, current_control, current_mem);
		final_ctl->set_req(final_slot, current_control);
		final_mem->set_req(final_slot, current_mem);
		final_io ->set_req(final_slot, eliminated->in(TypeFunc::I_O));
		final_arr->set_req(final_slot, arrcpy->in(ArrayCopyNode::Src));
		final_slot++;

		_igvn.set_delay_transform(false);
		_igvn.transform(allocateArrayNode);
		_igvn.transform(arrcpy);
		_igvn.transform(out_ctrl);
		_igvn.transform(out_mem);

		current_control = yes;
		return true;
	}

	// Start case (3)
	// The new array will fit without touching next object (or free space) iff
	// src + (copy_len + len_align) + header_sz < src_len + src_len_align, where
	// src_len_align is additional elements of src which can be put into object space,
	// tail_start <= (copy_len + len_align), and
	// len_align may be != src_len_align

  Node* tail_size = transform_later(new SubLNode(src_len_aligned, tail_start));
	      tail_size = transform_later(new SubLNode(tail_size, elements_per_header));

	// All calculations are 64 bit wide, so overflow can't happen as lengths are 32 bit wide
	// TODO Is above really true form hotspot perspective ?

	// if tail_size < 0, source is not big enough to carry even empty array

  // Garbage Collector Destroyer
  // tail_size = transform_later(new AddINode(tail_size, transform_later(ConINode::make(1))));



	// Need to calculate this way, instead of tail_addr  = array_element_address(src, tail_start, element_type), as
	// new CastPPNode(src, TypeOopPtr::BOTTOM), nor new CastX2PNode(new CastP2XNode(current_control, src))
	// doesn't work, 2nd returns source identity
	int header_size = -1; // Not used, helper
	Node* tail_addr;
	tail_addr = transform_later(new CastP2XNode(current_control, src));
	tail_addr = transform_later(new AddXNode(tail_addr,
	                                         transform_later(new LShiftXNode(tail_start, element_sz_log_node_i))));
  tail_addr = transform_later(new CastX2PNode(tail_addr));
	current_mem       = initialize_object_header(current_control, current_mem, tail_addr, arrcpy->in(ArrayCopyNode::SrcKlass), tail_size, header_size);
	// Ensure header is seen before new size
	insert_mem_bar(&current_control, &current_mem, Op_MemBarRelease);

	// And finish changes by setting new array length
	set_src_length_with_membar(tail_start, current_control, current_mem);

	MergeMemNode* final_merge = transform_later(MergeMemNode::make(start_mem));
	int alias_idx = C->get_alias_index(final_phi_addr);
	final_merge->set_memory_at(alias_idx, current_mem);
	current_mem = final_merge;



  // Now we have to replace all dest edges with Phi, expect this copy
  // Could be done with replace edge but additional validation is warm welcome



//
//	_igvn.add_users_to_worklist(start_ctl);

	//_igvn.set_delay_transform(true);
	//arrcpy->dump();
////	for (DUIterator_Last imin, i = out_ctrl->last_outs(imin); i >= imin; --i) {
////		Node* n = out_ctrl->last_out(i);
////		_igvn.hash_delete(n);
////		n->replace_edge(out_ctrl, final_ctl);
////	}
//	_igvn.add_users_to_worklist(final_ctl);
//	_igvn.add_users_to_worklist(out_ctrl->in(TypeFunc::Control));
//
//	// Replace original out current_mem with final_mem
//	for (DUIterator_Last imin, i = out_mem->last_outs(imin); i >= imin; --i) {
//		Node* n = out_mem->last_out(i);
//		_igvn.hash_delete(n);
//		n->replace_edge(out_mem, final_mem);
//	}
//	_igvn.add_users_to_worklist(final_mem);
//	_igvn.add_users_to_worklist(final_mem->in(TypeFunc::Control));
//
//	final_mem->set_req(1, out_mem);
//	final_mem->set_req(2, arrcpy->in(TypeFunc::Memory));
//	final_mem->set_req(3, arrcpy->in(TypeFunc::Memory));
//
//	final_ctl->set_req(1, out_ctrl);
//	final_mem->set_req(1, out_mem);
//
//	// Generates base check dst len == cpy len
//	generate_lengths_same_checks(orignal_control);
//
//	_igvn.transform(allocateArrayNode);



  // (1) copy_length == src_length
//  CmpINode*    leneq_cmp   = transform_later(new CmpINode(arrcpy->in(ArrayCopyNode::SrcLen), len));
//  BoolNode*    leneq_bool  = transform_later(new BoolNode(leneq_cmp, BoolTest::eq));
//  IfNode*      leneq_if    = transform_later(new IfNode(this->lengths_same_true, leneq_bool, PROB_FAIR, COUNT_UNKNOWN));
//  IfTrueNode*  leneq_true  = transform_later(new IfTrueNode(leneq_if));
//  IfFalseNode* leneq_false = transform_later(new IfFalseNode(leneq_if));

  // (3) src_length - minimum array size > copy_length
  // Need to check if src has enough space to put array header
  // Transform minimum array size to destination elements count
  // And check if src_len - min_elements <= copy length
  // TODO For smaller sizes Object can be put to avoid extra bytes for array length
  // TODO Add negative and overflow checks (are those needed?)
//

//  ConINode*    min_elements_const = transform_later(ConINode::make(min_elements));
//  SubINode*    min_len_subtract   = transform_later(new SubINode(arrcpy->in(ArrayCopyNode::SrcLen), min_elements_const));
//  CmpINode*    min_len_comp       = transform_later(new CmpINode(min_len_subtract, len));
//  BoolNode*    min_len_bool       = transform_later(new BoolNode(min_len_comp, BoolTest::ge));
//  IfNode*      min_len_if         = transform_later(new IfNode(leneq_false, min_len_bool, PROB_FAIR, COUNT_UNKNOWN));
//  IfTrueNode*  min_len_true       = transform_later(new IfTrueNode(min_len_if));
//  IfFalseNode* min_len_false      = transform_later(new IfFalseNode(min_len_if));

  // Connect final "slow(er) path"
//  out_ctrl->replace_by(region);
//  region->set_req(1, out_ctrl);
//
//  for (DUIterator i = region->outs(); region->has_out(i); i++) {
//    transform_list.append(region->out(i));
//  }
//
//  for (int i=0; i < transform_list.length(); i++) {
//    _igvn.transform(transform_list.at(i));
//  }

//  _igvn.transform(out_ctrl);

  //region->set_req(1, iff_true);
  //arrcpy->set_req(TypeFunc::Control, region);

//  Node *frame1 = transform_later(new ParmNode( C->start(), TypeFunc::FramePtr ));
//  Node *halt1 = transform_later(new HaltNode(leneq_true, frame1));
//  C->root()->add_req(halt1);
//  Node *frame2 = transform_later(new ParmNode( C->start(), TypeFunc::FramePtr ));
//  Node *halt2 = transform_later(new HaltNode(min_len_true, frame2));
//  C->root()->add_req(halt2);
//  halt2->dump();
//
//  arrcpy->replace_by(ac2);

//  _igvn.transform(arrcpy);

  return true;

}

void EliminateArrayCopyPhase::separate_eliminated_nodes(Node *out_control, Node *out_memory, Node *out_io) {
	// Insert slow path region to gather control if length check fails and connect eliminated nodes
	// to it
	const int final_slots = 2;
	slow_path = transform_later(new RegionNode(final_slots + 1));
	eliminated->set_req(TypeFunc::Control, slow_path);

	// Create final control region and final memory, io and val Phi nodes
	final_phi_addr = TypeRawPtr::BOTTOM;
	final_ctl      = transform_later(new RegionNode(final_slots + 1)); // Bottom 'surround' to gether checks
	final_mem      = transform_later(new PhiNode(final_ctl, Type::MEMORY, final_phi_addr));
	final_io       = transform_later(new PhiNode(final_ctl, Type::ABIO));
	final_arr      = transform_later(new PhiNode(final_ctl, arrcpy->in(ArrayCopyNode::Dest)->Value(&_igvn)));

	// Make finals phi big enaugh
	Node* top = C->top();
	final_ctl->ins_req(final_slots, top);
	final_mem->ins_req(final_slots, top);
	final_io ->ins_req(final_slots, top);
	final_arr->ins_req(final_slots, top);

	// Replace original out control & memory with final control & memory
	_igvn.insert_after(out_control, final_ctl);
	final_ctl->set_req(1, out_control);

	_igvn.insert_after(out_memory, final_mem);
	final_mem->set_req(1, out_memory);

	_igvn.insert_after(out_io, final_io);
	final_io->set_req(1, out_io);

	// Add dest switch. Some of dest edges goes to array copy, and still should go, the purpose of separation
	// is to conditionally switch src / dest, but control still can reach array copy.

	Node* dest = arrcpy->in(ArrayCopyNode::Dest);
	_igvn.insert_after(arrcpy->in(ArrayCopyNode::Dest), final_arr);

	// Insertion set array copy dest to final_arr, this would crate broken flow
	// Set back array copy destination
	int count = arrcpy->replace_edge(final_arr, dest);
	if (count != 2) {
		assert(count == 2, "Argument + stack == 2");
		C->record_failure("Unexpected usages of array copy destination. Expected 2");
	}
  final_arr->set_req(1, dest);
}

void EliminateArrayCopyPhase::generate_lengths_same_checks(Node *control) {
	CmpINode*    cantrunk_cmp   = transform_later(new CmpINode(arrcpy->in(ArrayCopyNode::DestLen), arrcpy->in(ArrayCopyNode::Length)));
	BoolNode*    cantrunk_bool  = transform_later(new BoolNode(cantrunk_cmp, BoolTest::eq));
	make_if(control, cantrunk_bool, lengths_same_true, lengths_same_false);
}

bool EliminateArrayCopyPhase::collect_array_allocations(Node *start, GrowableArray<Node *> &roots) {
  GrowableArray<Node*> work_list;
  work_list.append(start);

  bool roots_valid = true;
  for (int i=0; i < work_list.length(); i++) {
    Node* n = work_list.at(i);
    switch(n->Opcode()) {
      case Op_Phi: {
        // Put all inputs to worklist
        PhiNode *phi = n->as_Phi();
        for (uint i = PhiNode::Input; i < phi->req(); i++)
          work_list.append_if_missing(phi->in(i));
        break;
      }

      case Op_CheckCastPP: {
        CheckCastPPNode *check_cast = n->as_CheckCastPP();
        ProjNode *proj = check_cast->in(1)->isa_Proj();
        if (proj) {
          AllocateArrayNode* alloc = proj->in(0)->as_AllocateArray();
          if (alloc)
            roots.append_if_missing(alloc);
          else
            roots_valid = false;
        }else {
          roots_valid = false;
        }
        break;
      }

      default:
        roots_valid = false;
    }
  }

  return roots_valid;
}

bool EliminateArrayCopyPhase::collect_array_usages(GrowableArray<Node *> &roots, GrowableArray<Node *> &accepted, GrowableArray<Node*> &usages) {
  GrowableArray<Node*> &work_list = helper;
  for (int i = 0; i < roots.length(); i++) {
    Node *root = roots.at(i);
    int found_check_casts = 0;
    for (DUIterator j = root->outs(); root->has_out(j); j++) {
      if (ProjNode *proj = root->out(j)->isa_Proj()) {
        if (proj->_con == TypeFunc::Parms) {
          for (DUIterator k = proj->outs(); proj->has_out(k); k++) {
            Node* out = proj->out(k);

            if (out->is_CheckCastPP()) {
              work_list.append_if_missing(out);
              found_check_casts++;
            }else if (out->is_Initialize()) {
              // skip
            }else {
              return false;
            }
          }
        }
      } else {
        return false;
      }
    }
    if (found_check_casts != 1)
      return false;
  }

  for (int i=0; i < work_list.length(); i++) {
    Node *n = work_list.at(i);

    bool invalid = false;
		const Node* top = C->top();

	  int opcode = n->Opcode();
		Node* in_control = n->in(TypeFunc::Control);

    switch(opcode) {
	    case Op_AddP:
	    case Op_LoadB:
	    case Op_LoadUB:
	    case Op_LoadS:
	    case Op_LoadUS:
	    case Op_LoadI:
	    case Op_LoadL:
	    case Op_LoadF:
	    case Op_LoadD:
	    case Op_AndI:
	    case Op_AndL:
	    case Op_CmpF:
	    case Op_CmpI:
	    case Op_CmpL:
	    case Op_CmpD:
	    case Op_Bool:
	    case Op_URShiftL:
	    case Op_URShiftI:
	    case Op_ConvI2L:
	    case Op_ConvI2F:
	    case Op_ConvI2D:
	    case Op_ConvL2I:
	    case Op_ConvL2F:
	    case Op_ConvL2D:
	    case Op_ConvF2I:
	    case Op_ConvF2L:
	    case Op_ConvF2D:
	    case Op_ConvD2I:
	    case Op_ConvD2L:
	    case Op_ConvD2F:{
		    // Shifts, ands are often used in [].hashCode()
		    if (in_control != NULL && in_control != top) {
			    usages.append_if_missing(n);
		    }
		    // Always append outs, as those can be base for later calculations
		    n->add_outs_to_list(work_list);
		    break;
	    }
	    case Op_If:
	    case Op_Phi:
	    case Op_StoreB:
	    case Op_StoreC:
	    case Op_StoreI:
	    case Op_StoreL:
	    case Op_StoreF:
	    case Op_StoreD: {
		    if (in_control != NULL && in_control != top) {
			    usages.append_if_missing(n);
		    }else {
			    assert(false, "Store should have control");
		    }
		    break;
	    }
	    case Op_CheckCastPP:
		    n->add_outs_to_list(work_list);
		    break;
	    case Op_CallStaticJava:
		    //TODO Call can return src, if passed as argument - need more elaboration
		    usages.append_if_missing(n);
		    break;
	    default:
		    if (!accepted.contains(n))
		      invalid = true;
    }

    if (invalid) {
      tty->print("ArrayCopyElimination: Unexpected node for usage analyse: ");
      n->dump_comp("\n", tty);
      return false;
    }
  }
  return true;
}

Node* EliminateArrayCopyPhase::find_parent_skip_alloc(Node *sub, node_idx_t idx, GrowableArray<Node *> &stop_on,
                                                    GrowableArray<Node *> &helper) {
	Node* result = NULL;

	if (NotANode(sub) || sub->is_Root() || helper.contains(sub) || stop_on.contains(sub))
		return NULL;

	helper.append(sub);

	if (sub->_idx == idx)
		return sub;

	if (sub->is_Region()) {
		for (uint i=1; i < sub->req(); i++) {
			result = find_parent_skip_alloc(sub->in(i), idx, stop_on, helper);
			if (result)
				break;
		}
	}else if (sub->is_CFG() || sub->is_Store() || sub->is_Call() || sub->is_Load() ||
					  sub->is_CheckCastPP() || sub->is_Initialize() || sub->is_Catch() ||
					  sub->is_Phi()) {
		result = find_parent_skip_alloc(sub->in(TypeFunc::Control), idx, stop_on, helper);
	}else if (sub->is_Proj() && sub->as_Proj()->_con == TypeFunc::Control) {
		result = find_parent_skip_alloc(sub->in(TypeFunc::Control), idx, stop_on, helper);
	}else {
		tty->print("EliminateArrayCopy: Unexpected node when finding control: ");
		sub->dump();
		return sub;
	}

	return result;
}

#ifdef ASSERT
void EliminateArrayCopyPhase::assert_reaches_root(Node* use, Node* dst) {
	// Is this check needed, does tight alloc guarants this
	for (DUIterator i; dst->has_out(i); i++) {
		Node *use = dst->out(i);
		if (use != arrcpy && use->is_CFG()) {
			helper.clear();
			assert(find_parent_skip_alloc(use, arrcpy->_idx, helper2, helper) == arrcpy,
			       "Every use should be after copy");
		}
	}
}
#endif