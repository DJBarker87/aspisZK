import XRz_HybridTx1
import XRz_HybridPrepareRaw
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRz_HybridTx1Raw
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (physical proof : Slice U8) (split : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) :
 XRz_HybridTx1.tx1 sampler.low_base_p_digits D pub physical proof split hash obs=
 verifier.candidate.tx1 D pub physical proof split hash obs := by
 unfold XRz_HybridTx1.tx1 verifier.candidate.tx1
 simp only [XRz_HybridPrepareRaw.source]
 rfl
#print axioms source
end XRz_HybridTx1Raw
