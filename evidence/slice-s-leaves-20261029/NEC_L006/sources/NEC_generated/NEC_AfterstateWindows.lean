import NEC_AfterstateBox
import NDM_CommonWindows
set_option autoImplicit false
namespace NEC_AfterstateWindows
open Aeneas Aeneas.Std
open NEC_AfterstateBox

structure Fields (actual expected : Value) : Prop where
 next : actual.next_pair_index=expected.next_pair_index
 root : NDM_CommonWindows.Window actual.next_root expected.next_root
 frontier : NDM_CommonWindows.Nested actual.next_frontier expected.next_frontier

/-- All actual afterstate fields, without canonicality restrictions. -/
theorem assemble (actual expected : Value) (fields : Fields actual expected) :
 actual=expected := by
 have next := fields.next
 have root := NDM_CommonWindows.array_ext _ _ fields.root
 have frontier := NDM_CommonWindows.nested_ext _ _ fields.frontier
 cases actual
 cases expected
 simp_all

/-- Exact native caller geometry: the late-public record is 1520 bytes and
 its final afterstate starts at 32+800. Input association is caller-owned. -/
theorem caller_domain (parent child : Slice U8)
 (length : parent.val.length=1520)
 (association : child.val=parent.val.drop 832) : PacketDomain child := by
 unfold PacketDomain
 rw [association,List.length_drop,length]

#print axioms assemble
#print axioms caller_domain
end NEC_AfterstateWindows
