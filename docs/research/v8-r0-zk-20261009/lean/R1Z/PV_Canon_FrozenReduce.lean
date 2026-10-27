import R1Z.PV_Canon_Reduce
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result
 theorem checked_reduce (x : U64) :
    ∃ z, AspisR1ProducerChecked47.field.reduce_u64 x = .ok z ∧ M z := by
  obtain ⟨z,hz,_,hc⟩ := AspisR1.ExtractedCurrentReducer.current_reduce_mod x
  refine ⟨z,?_,hc⟩
  rw [ProverCommitPrimitive47.reduce,hz]
#print axioms checked_reduce
end R1Z.PV_Canon
