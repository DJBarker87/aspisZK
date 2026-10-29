import R1Z.PV_RunJoin_FoldCell44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceLength48
open Aeneas Aeneas.Std ProverRwFull
open ProverCommitWideOps48
variable [ExternalTypes]

theorem array (n : Usize) (q : Nat → Raw) :
    (Array.to_slice (PV_RunJoin_FoldCell44.array n q)).length=n.val :=
  Array.length_to_slice _

theorem first (q : Nat → Raw) :
    (Array.to_slice (PV_RunJoin_FoldCell44.array 1024#usize q)).length/4≤256 := by
  rw [array]
  decide

theorem second (q : Nat → Raw) :
    (Array.to_slice (PV_RunJoin_FoldCell44.array 256#usize q)).length/4≤256 := by
  rw [array]
  decide
#print axioms array
#print axioms first
#print axioms second
end R1Z.PV_RunJoin_SourceLength48
