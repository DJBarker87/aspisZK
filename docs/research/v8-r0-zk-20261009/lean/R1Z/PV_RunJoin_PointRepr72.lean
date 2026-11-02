import R1Z.PV_RunJoin_PointArray34
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PointRepr72
open Aeneas Aeneas.Std ProverRwFull
abbrev Point := Array aspis_core.field.QM31 10#usize

def cells (a : Point) (i : Nat) : ProverCommitPrimitive47.Old.Q :=
  PV_RunJoin_FieldData34.old (a.val[i%10]'(by rw [a.property];exact Nat.mod_lt _ (by decide)))

theorem complete (a : Point) : PV_RunJoin_PointArray34.array (cells a)=a := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp only [PV_RunJoin_PointArray34.array,ProverCommitArray49.array,List.length_ofFn,a.property]
  · intro i hi hi'
    have bound : i<10 := by
      simpa only [PV_RunJoin_PointArray34.array,ProverCommitArray49.array,List.length_ofFn,UScalar.ofNatCore_val_eq] using hi
    simp only [PV_RunJoin_PointArray34.array,ProverCommitArray49.array,List.getElem_ofFn,cells,
      Nat.mod_eq_of_lt bound,PV_RunJoin_FieldData34.source_old]

#print axioms cells
#print axioms complete
end R1Z.PV_RunJoin_PointRepr72
