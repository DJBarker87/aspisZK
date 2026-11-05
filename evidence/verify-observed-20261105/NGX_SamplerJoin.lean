import NGX_PrefixSource
import NGT_COMBINED_IMPORT
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NGX_SamplerJoin
/-- Reuse the committed division construction, on the same complete digest
block. No desired sampler equality or chosen output is a premise. -/
theorem total (block : Array U8 32#usize) :
 ∃ (digits : List Nat) (last : List UInt32) (q : aspis_core.field.QM31),
 LPk_Induction.Digits 4 (SamplerBytePass.digits block) digits last ∧
 NGT_NBA_Rho.coordinates q=digits ∧ AspisR1PublicPreparation.sampler.qm31_sample block=ok q :=
 NGT_NBL_RhoConstruct.source block
#print axioms total
end AspisR1.NGX_SamplerJoin
