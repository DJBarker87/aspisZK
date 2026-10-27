import PV_B3_CanonicalReduce
import PV_B3_CanonicalSource
set_option autoImplicit false
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result
theorem current_mreduce (x : U64) :
    ∃ z, PV_B3_Copy_117.aspis_core.field.M31.reduce_u64 x = .ok z ∧ M z := by
  obtain ⟨z,hz,hc⟩ := current_reduce x
  refine ⟨z,?_,hc⟩
  simp only [PV_B3_Copy_117.aspis_core.field.M31.reduce_u64,hz,bind_tc_ok]
#print axioms current_mreduce
end PV_B3_Canonical
