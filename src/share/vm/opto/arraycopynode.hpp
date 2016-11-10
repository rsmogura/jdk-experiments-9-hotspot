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

#ifndef SHARE_VM_OPTO_ARRAYCOPYNODE_HPP
#define SHARE_VM_OPTO_ARRAYCOPYNODE_HPP

#include "opto/callnode.hpp"
#include "opto/macro.hpp"

class GraphKit;

class ArrayCopyNode : public CallNode {
private:

  // What kind of arraycopy variant is this?
  enum {
    None,            // not set yet
    ArrayCopy,       // System.arraycopy()
    CloneBasic,      // A clone that can be copied by 64 bit chunks
    CloneOop,        // An oop array clone
    CopyOf,          // Arrays.copyOf()
    CopyOfRange      // Arrays.copyOfRange()
  } _kind;

#ifndef PRODUCT
  static const char* _kind_names[CopyOfRange+1];
#endif
  // Is the alloc obtained with
  // AllocateArrayNode::Ideal_array_allocation() tighly coupled
  // (arraycopy follows immediately the allocation)?
  // We cache the result of LibraryCallKit::tightly_coupled_allocation
  // here because it's much easier to find whether there's a tightly
  // couple allocation at parse time than at macro expansion time. At
  // macro expansion time, for every use of the allocation node we
  // would need to figure out whether it happens after the arraycopy (and
  // can be ignored) or between the allocation and the arraycopy. At
  // parse time, it's straightforward because whatever happens after
  // the arraycopy is not parsed yet so doesn't exist when
  // LibraryCallKit::tightly_coupled_allocation() is called.
  bool _alloc_tightly_coupled;

  bool _arguments_validated;

  static const TypeFunc* arraycopy_type() {
    const Type** fields = TypeTuple::fields(ParmLimit - TypeFunc::Parms);
    fields[Src]       = TypeInstPtr::BOTTOM;
    fields[SrcPos]    = TypeInt::INT;
    fields[Dest]      = TypeInstPtr::BOTTOM;
    fields[DestPos]   = TypeInt::INT;
    fields[Length]    = TypeInt::INT;
    fields[SrcLen]    = TypeInt::INT;
    fields[DestLen]   = TypeInt::INT;
    fields[SrcKlass]  = TypeKlassPtr::BOTTOM;
    fields[DestKlass] = TypeKlassPtr::BOTTOM;
    const TypeTuple *domain = TypeTuple::make(ParmLimit, fields);

    // create result type (range)
    fields = TypeTuple::fields(0);

    const TypeTuple *range = TypeTuple::make(TypeFunc::Parms+0, fields);

    return TypeFunc::make(domain, range);
  }

  ArrayCopyNode(Compile* C, bool alloc_tightly_coupled);

  intptr_t get_length_if_constant(PhaseGVN *phase) const;
  int get_count(PhaseGVN *phase) const;
  static const TypePtr* get_address_type(PhaseGVN *phase, Node* n);

  Node* try_clone_instance(PhaseGVN *phase, bool can_reshape, int count);
  bool prepare_array_copy(PhaseGVN *phase, bool can_reshape,
                          Node*& adr_src, Node*& base_src, Node*& adr_dest, Node*& base_dest,
                          BasicType& copy_type, const Type*& value_type, bool& disjoint_bases);
  void array_copy_test_overlap(PhaseGVN *phase, bool can_reshape,
                               bool disjoint_bases, int count,
                               Node*& forward_ctl, Node*& backward_ctl);
  Node* array_copy_forward(PhaseGVN *phase, bool can_reshape, Node* ctl,
                           Node* start_mem_src, Node* start_mem_dest,
                           const TypePtr* atp_src, const TypePtr* atp_dest,
                           Node* adr_src, Node* base_src, Node* adr_dest, Node* base_dest,
                           BasicType copy_type, const Type* value_type, int count);
  Node* array_copy_backward(PhaseGVN *phase, bool can_reshape, Node* ctl,
                            Node *start_mem_src, Node* start_mem_dest,
                            const TypePtr* atp_src, const TypePtr* atp_dest,
                            Node* adr_src, Node* base_src, Node* adr_dest, Node* base_dest,
                            BasicType copy_type, const Type* value_type, int count);
  bool finish_transform(PhaseGVN *phase, bool can_reshape,
                        Node* ctl, Node *mem);
  static bool may_modify_helper(const TypeOopPtr *t_oop, Node* n, PhaseTransform *phase, ArrayCopyNode*& ac);

public:

  enum {
    Src   = TypeFunc::Parms,
    SrcPos,
    Dest,
    DestPos,
    Length,
    SrcLen,
    DestLen,
    SrcKlass,
    DestKlass,
    ParmLimit
  };

  // Results from escape analysis for non escaping inputs
  const TypeOopPtr* _src_type;
  const TypeOopPtr* _dest_type;

  static ArrayCopyNode* make(GraphKit* kit, bool may_throw,
                             Node* src, Node* src_offset,
                             Node* dest,  Node* dest_offset,
                             Node* length,
                             bool alloc_tightly_coupled,
                             Node* src_klass = NULL, Node* dest_klass = NULL,
                             Node* src_length = NULL, Node* dest_length = NULL);

  void connect_outputs(GraphKit* kit);

  bool is_arraycopy()             const  { assert(_kind != None, "should bet set"); return _kind == ArrayCopy; }
  bool is_arraycopy_validated()   const  { assert(_kind != None, "should bet set"); return _kind == ArrayCopy && _arguments_validated; }
  bool is_clonebasic()            const  { assert(_kind != None, "should bet set"); return _kind == CloneBasic; }
  bool is_cloneoop()              const  { assert(_kind != None, "should bet set"); return _kind == CloneOop; }
  bool is_copyof()                const  { assert(_kind != None, "should bet set"); return _kind == CopyOf; }
  bool is_copyof_validated()      const  { assert(_kind != None, "should bet set"); return _kind == CopyOf && _arguments_validated; }
  bool is_copyofrange()           const  { assert(_kind != None, "should bet set"); return _kind == CopyOfRange; }
  bool is_copyofrange_validated() const  { assert(_kind != None, "should bet set"); return _kind == CopyOfRange && _arguments_validated; }

  void set_arraycopy(bool validated)   { assert(_kind == None, "shouldn't bet set yet"); _kind = ArrayCopy; _arguments_validated = validated; }
  void set_clonebasic()                { assert(_kind == None, "shouldn't bet set yet"); _kind = CloneBasic; }
  void set_cloneoop()                  { assert(_kind == None, "shouldn't bet set yet"); _kind = CloneOop; }
  void set_copyof(bool validated)      { assert(_kind == None, "shouldn't bet set yet"); _kind = CopyOf; _arguments_validated = validated; }
  void set_copyofrange(bool validated) { assert(_kind == None, "shouldn't bet set yet"); _kind = CopyOfRange; _arguments_validated = validated; }

  virtual int Opcode() const;
  virtual uint size_of() const; // Size is bigger
  virtual bool guaranteed_safepoint()  { return false; }
  virtual Node *Ideal(PhaseGVN *phase, bool can_reshape);

  virtual bool may_modify(const TypeOopPtr *t_oop, PhaseTransform *phase);

  bool is_alloc_tightly_coupled() const { return _alloc_tightly_coupled; }

  static bool may_modify(const TypeOopPtr *t_oop, MemBarNode* mb, PhaseTransform *phase, ArrayCopyNode*& ac);
  bool modifies(intptr_t offset_lo, intptr_t offset_hi, PhaseTransform* phase, bool must_modify);

	/// Matches ideal Array Copy, when not match output arguments may be clobbered
	/// @return true if pattern matches
  static bool Ideal_ArrayCopy(ArrayCopyNode* ac, Node*& input_ctrl, CatchProjNode*& out_control, ProjNode*& out_memory, ProjNode*& out_io);
#ifndef PRODUCT
  virtual void dump_spec(outputStream *st) const;
  virtual void dump_compact_spec(outputStream* st) const;
#endif
};

class EliminateArrayCopyPhase : public PhaseMacroExpand {
private:
    ArrayCopyNode* arrcpy;

    Node* lengths_same_true;
    Node* lengths_same_false;

    /// Which node is eliminated (may not be arrcpy, but dst allocation)
    Node* eliminated;

    /// The type of output phi
    const TypePtr* final_phi_addr;

    /// Top region to gather slow paths, when generated checks fails
    Node* slow_path;

    /// Bottom region used to gather control paths, for slow and fast regions. First input is arrcpy (slow path)
    Node* final_ctl;

    /// Bottom phi selecting memory basing on checks control path (final_ctl), for slow and fast regions
    Node*    final_mem;

    /// Bottom phi selecting i/o basing on checks control path (final_ctl), for slow and fast regions
    Node*    final_io;

    /// Bottom phi selecting array basing on checks control path (final_ctl), for slow and fast regions
    Node*    final_arr;

    /// Helper variables, kept here to reduce memory pressure when array grows
    GrowableArray<Node*> helper, helper2;

    template<typename N> N* transform_later(N* n) {
      // equivalent to _gvn.transform in GraphKit, Ideal, etc.
      _igvn.register_new_node_with_optimizer(n);
      return n;
    }
protected:
		// Generate check if dst length equals copy length
    void  generate_lengths_same_checks(Node *control);

    void  generate_need_new_array_checks(Node* control);

    void separate_eliminated_nodes(Node *out_control, Node *out_memory, Node *out_io);

    void set_src_length_with_membar(Node* len, Node* &current_control, Node* &current_mem);

		debug_only(void assert_reaches_root(Node* use, Node* dst));
public:
    EliminateArrayCopyPhase(Compile* C, PhaseIterGVN &igvn) :
            PhaseMacroExpand(igvn, Eliminate_Array_Copy) {

    }

    void eliminate_all_array_copy();
    bool eliminate_single_array_copy(ArrayCopyNode* arrcpy);

    /// For given node collects all array allocations (there can be more than one, it's phi)
    static bool collect_array_allocations(Node *start, GrowableArray<Node*> &roots);

    /// Collects all array usages
    /// @param accepted nodes which are accepted and not traversed
    /// @return false if unexpected nodes has been been found
    bool collect_array_usages(GrowableArray<Node *> &roots, GrowableArray<Node *> &accepted, GrowableArray<Node*> &usages);

    /// Searches for control node with idx, stopping at stop_on.
    /// @param helper node list used to prevent circular travers
    static Node* find_parent_skip_alloc(Node* sub, node_idx_t idx, GrowableArray<Node *> &stop_on, GrowableArray<Node *> &helper);


};
#endif // SHARE_VM_OPTO_ARRAYCOPYNODE_HPP
