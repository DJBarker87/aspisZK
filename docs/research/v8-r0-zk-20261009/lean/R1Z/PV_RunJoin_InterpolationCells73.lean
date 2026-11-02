import R1Z.PV_RunJoin_InterpolationInput72
set_option autoImplicit false
namespace R1Z.PV_RunJoin_InterpolationCells73
open Aeneas Aeneas.Std ProverRwFull

theorem complete (p : Nat → aspis_core.field.QM31) (i : Nat) (hi : i<28) :
    PV_RunJoin_InterpolationInput72.cells (PV_RunJoin_MergeArray35.array p) i=p i := by
  simp only [PV_RunJoin_InterpolationInput72.cells,PV_RunJoin_MergeArray35.array,
    ProverCommitArray49.array,List.getElem_ofFn,Nat.mod_eq_of_lt hi]

#print axioms complete
end R1Z.PV_RunJoin_InterpolationCells73
