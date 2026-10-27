import R1Z.PV_CBL_FallbackFourModel
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackFourBind
open PV_CBL_FallbackArray4
set_option autoImplicit false
theorem expand {X : Type} (abef cdgh w k : A4) (next : A4×A4→Result X) :
    (PV_CBL_FallbackFourModel.source abef cdgh w k >>= next) =
    (do
      let t ← PV_CBL_FallbackBlock.sha_fallback_reference.add w k
      let c ← PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 cdgh abef t
      let u ← PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t
      let a ← PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 abef c u
      next (a,c)) := by
  simp only [PV_CBL_FallbackFourModel.source,bind_assoc_eq,bind_tc_ok]
#print axioms expand
end R1Z.PV_CBL_FallbackFourBind
