import SInt2_AcceptedPairClaims
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.RowShape_InstalledSlots
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace

/-- Exactly the verifier dictionary passed to sdkOps in accepted_pair_claims. -/
def verifierOps (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) : Ops :=
  NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children
    (ClaimsUnrolledFinish.install std B)

/-- The existing installation does not instantiate the shape body. -/
theorem shape_slot (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) :
    (verifierOps ops B std).op3 = ops.op3 := rfl

/-- The existing installation does not instantiate the canonical scan body. -/
theorem scan_slot (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) :
    (verifierOps ops B std).op4 = ops.op4 := rfl

/-- Link the projection check to the exact SDK installation, without selecting
another execution, cuts or dictionary. -/
theorem sdk_dictionary (adapterOps : AdapterRw.Ops) (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) :
    ClaimsUnrolledSdk.sdkOps adapterOps ops B std =
      AspisS6CurrentFirstInstallation.install adapterOps (verifierOps ops B std) := rfl

#print axioms shape_slot
#print axioms scan_slot
#print axioms sdk_dictionary
end AspisR1.RowShape_InstalledSlots
end
