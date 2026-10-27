import R1Z.PV_Canon_Reduce
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result
theorem current_mreduce (x : U64) :
    ∃ z, ProverRwP7CurrentFieldSource.aspis_core.field.M31.reduce_u64 x = .ok z ∧ M z := by
  obtain ⟨z,hz,hc⟩ := current_reduce x
  refine ⟨z,?_,hc⟩
  simp only [ProverRwP7CurrentFieldSource.aspis_core.field.M31.reduce_u64,hz,bind_tc_ok]
#print axioms current_mreduce
end R1Z.PV_Canon
