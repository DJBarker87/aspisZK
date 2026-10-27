import XRz_HybridPrepare
import XRz_HybridPreparedRaw
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRz_HybridPrepareRaw
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
 XRz_HybridPrepare.prepare sampler.low_base_p_digits D pub proof hash obs g=
 verifier.candidate.prepare D pub proof hash obs g := by
 unfold XRz_HybridPrepare.prepare verifier.candidate.prepare
 simp only [XRz_HybridPreparedRaw.source]
 rfl
#print axioms source
end XRz_HybridPrepareRaw
