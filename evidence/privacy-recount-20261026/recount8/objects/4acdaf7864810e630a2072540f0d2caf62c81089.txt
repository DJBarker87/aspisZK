import R1Z.PV_RunJoin_SourceScalar
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SourceSbox
open Aeneas Aeneas.Std Result R0Z.WriterRefine
variable {K : Type} [Field K] [CharP K 2147483647]

/-- Unconditional source refinement of the nonlinear scalar layer. It
composes the three actual extracted multiplications symbolically, including
canonical output; no concrete permutation or root recurrence is reduced. -/
theorem pow5 (value : U32) :
    ∃ out, BuilderForestAdmissionPort.poseidon2.pow5 value = ok out ∧
      out.val < 2147483647 ∧ liftU (K := K) out = (liftU value)^5 := by
  obtain ⟨square,hsquare,csquare,msquare⟩ := PV_RunJoin_SourceScalar.forest_mul (K := K) value value
  obtain ⟨fourth,hfourth,cfourth,mfourth⟩ := PV_RunJoin_SourceScalar.forest_mul (K := K) square square
  obtain ⟨out,hout,canonical,meaning⟩ := PV_RunJoin_SourceScalar.forest_mul (K := K) fourth value
  refine ⟨out,?_,canonical,?_⟩
  · rw [BuilderForestAdmissionPort.poseidon2.pow5,hsquare]
    simp only [bind_tc_ok]
    rw [hfourth]
    simp only [bind_tc_ok]
    exact hout
  · rw [meaning,mfourth,msquare]
    ring

#print axioms pow5
end R1Z.PV_RunJoin_SourceSbox
