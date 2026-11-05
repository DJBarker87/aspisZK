import RPz7_SAP_PrepareOwner
import NHS_FieldConversion
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_PrepareFields
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation
-- Extends the retained zero-input model theorem to every input scratch.
-- It is a model consumer-domain theorem; native constructor packet is NHS_.
theorem installed (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    ∀ {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (p : verifier.Prepared),
    verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops (F3M_CircleSource.install B) std)
      D pub proof hash none input=ok (.Ok p,scratch) →
    NGC_PreparationBoundary.Fields (Tx1Q_Carriers.prepared p) := by
  intro H D hash pub proof input scratch p success
  apply NHS_FieldConversion.source
  obtain ⟨expanded,y1,view,sem,out,rs,wide,same,verify,outEq,reached,canon,alpha,claim⟩ :=
    SAP_OpeningCuts.opening ops (F3M_CircleSource.install B) std D hash pub proof p
      input scratch success
  have variant : (retainedView view).variant=AspisR1PublicPreparation.transport.Variant.S2 := by
    change retainedVariant view.variant=_
    rw [sourceView_variant proof expanded y1 view wide]
    rfl
  have shape := SAP_OpeningShape.fields (retainedDigest D) (retainedSem sem) (retainedView view)
    hash out rs variant reached
  have semantic := SAP_SemanticCanonical.alpha AspisS1ExtractedRoundChildren.children
    (ClaimsUnrolledFinish.install std (F3M_CircleSource.install B)) D pub expanded hash sem verify
  obtain ⟨z0,z1,z,canon0,canon1⟩ := SAP_SemanticCircles.coordinates
    AspisS1ExtractedRoundChildren.children B std D pub expanded hash sem verify
  rw [←outEq]
  apply SAP_PreparedFields.fields out shape.1 shape.2.2.2.1 canon.1 canon.2 alpha shape.2.2.2.2
  · rw [shape.2.1];exact semantic
  · exact shape.2.2.1.trans z
  · exact canon0
  · exact canon1
  · exact claim

#print axioms installed
end AspisR1.NHS_PrepareFields
