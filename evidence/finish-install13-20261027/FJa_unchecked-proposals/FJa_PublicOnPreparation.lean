import FJa_PublicBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_PublicOnPreparation
open Aeneas Aeneas.Std Result
open AspisR1TerminalDigestBindingCandidate.SemanticPublicPreparationCopy
/-- Exact installed semantic public and all FIz-required word bounds derive
from the SAME successful public transcript preparation. -/
theorem value {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (s : AspisR1TerminalDecoder.PublicBinding.Statement) (hash : H)
    (c1 : Array U8 32#usize) (out : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (p : FJa_PublicCopy.Public)
    (prepared : AspisR1PublicPreparation.r1_semantic.public_transcript D
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s) hash c1=ok (.Ok out))
    (constructed : FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.semantic
      (FIq_Carriers.toPublic (AspisR1PublicPreparation.PreparationBinding.preparationPublic s))=ok p) :
    p=FJa_PublicCopy.native (copyFromStatement s) ∧ FJa_PublicBounds.Bounds p := by
  have same := Result.ok.inj ((FJa_PublicCopy.on_statement s).symm.trans constructed)
  subst p
  exact ⟨rfl,FJa_PublicBounds.from_copy _
    (AspisR1TerminalDigestBindingCandidate.SemanticPublicFieldsCanonical.actual_preparation_fields_canonical D s hash c1 out prepared)⟩
#print axioms value
end AspisR1.FJa_PublicOnPreparation
end
