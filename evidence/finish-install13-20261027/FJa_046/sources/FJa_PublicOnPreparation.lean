import FJa_PublicBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_PublicOnPreparation
open Aeneas Aeneas.Std Result
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
    p=FJa_PublicCopy.native (AspisR1PublicPreparation.PreparationBinding.preparationPublic s) ∧ FJa_PublicBounds.Bounds p := by
  have same := Result.ok.inj ((FJa_PublicCopy.on_statement (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)).symm.trans constructed)
  subst p
  exact ⟨rfl,FJa_PublicBounds.from_raw s
    (AspisR1PublicPreparation.ActualPublicFieldBounds.public_transcript_fields_canonical D s hash c1 out prepared)⟩
#print axioms value
end AspisR1.FJa_PublicOnPreparation
end
