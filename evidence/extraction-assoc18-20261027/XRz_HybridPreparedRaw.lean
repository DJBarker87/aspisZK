import XRz_HybridPrepared
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRz_HybridPreparedRaw
/-- The substitution boundary is exactly the excluded low sampler. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
 XRz_HybridPrepared.prepared sampler.low_base_p_digits D sem v hash g=
 verifier.Prepared.new D sem v hash g := by
 unfold XRz_HybridPrepared.prepared verifier.Prepared.new
 simp only [XRz_HybridSampler.scalar,XRq_OrdinaryScalar.raw]
 rfl
#print axioms source
end XRz_HybridPreparedRaw
