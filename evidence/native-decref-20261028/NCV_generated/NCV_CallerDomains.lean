import NCV_CastHelpers
import NBX_SequenceDomains
set_option autoImplicit false
namespace NCV_CallerDomains
open Aeneas Aeneas.Std Result AspisR1

theorem master_identity (b : Slice U8) (length : b.val.length=384) :
    (JHg_FieldRead.segment b 64 144).val.length=144 :=
  JHg_FieldRead.length b 64 144 (by omega)

theorem master_policy (b : Slice U8) (length : b.val.length=384) :
    (JHg_FieldRead.segment b 208 104).val.length=104 :=
  JHg_FieldRead.length b 208 104 (by omega)

theorem checkpoint_bindings (b : Slice U8) (length : b.val.length=192) :
    (JHg_FieldRead.segment b 8 32).val.length=32 ∧
    (JHg_FieldRead.segment b 40 32).val.length=32 ∧
    (JHg_FieldRead.segment b 80 32).val.length=32 :=
  ⟨JHg_FieldRead.length b 8 32 (by omega),JHg_FieldRead.length b 40 32 (by omega),
    JHg_FieldRead.length b 80 32 (by omega)⟩

theorem lane_tree (b : Slice U8) (length : b.val.length=768) :
    (JHg_FieldRead.segment b 80 688).val.length=688 :=
  JHg_FieldRead.length b 80 688 (by omega)

theorem lane_frontier (level : Nat) (bound : level<20) :
    48+32*level+32 ≤ 688 ∧ level<64 := by omega

theorem master_row (lane : Nat) (bound : lane<8) :
    320+8*lane+8 ≤ 384 := by
  exact (NBX_SequenceDomains.master lane bound).2

theorem checkpoint_row (lane : Nat) (bound : lane<8) :
    112+8*lane+8 ≤ 192 := NBX_SequenceDomains.checkpoint_input lane bound

#print axioms master_identity
#print axioms master_policy
#print axioms checkpoint_bindings
#print axioms lane_tree
#print axioms lane_frontier
#print axioms master_row
#print axioms checkpoint_row
end NCV_CallerDomains
