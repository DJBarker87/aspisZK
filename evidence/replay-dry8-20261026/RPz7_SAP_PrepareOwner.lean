import RPz7_SAP_OpeningCuts
import RPz7_SAP_OpeningShape
import RPz7_SAP_SemanticCanonical
import RPz7_SAP_SemanticCircles
import RPz7_SAP_PreparedFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_PrepareOwner
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation

/-- Derive the complete immutable preparation contract from this installed
source; the circle slot is explicitly the shipped source wrapper. -/
theorem installed (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    WAdm_Domain.SessionAPrepare
      (RowShape_InstalledSlots.verifierOps ops (F3M_CircleSource.install B) std) := by
  constructor
  intro H D hash pub proof zero p scratch success
  obtain ⟨expanded,y1,view,sem,out,rs,wide,same,verify,outEq,reached,canon,alpha,claim⟩ :=
    SAP_OpeningCuts.opening ops (F3M_CircleSource.install B) std D hash pub proof p
      (Array.repeat 29#usize zero) scratch success
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
end AspisR1.SAP_PrepareOwner
end
