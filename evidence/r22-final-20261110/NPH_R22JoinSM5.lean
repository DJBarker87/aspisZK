import NPH_R22JoinSM4
import NOC_Op9Slot

/-! NPH_ (R22, SM step 4): the deployed op9 slot tie.
`slot_guarded`: for every host context and every public whose retained digest domain holds
(LIB_VPublicDomain.publicDigestDom (toRetainedPublic pub)), the literal installed op9 slot on
release `none` (NOC_Op9Slot.slot: S1SemanticInstallation.verify over the Claims-unrolled
deployed boundaries) equals the SAME semantic installation over `Bslot`, the record whose
mask/add/mul are the guarded NPH_R22JoinSM4.gmask/gadd/gmul. Its proof is the slot rfl
followed by NPH_R22JoinSM4.deployed_verify_guarded (the root-copy wrapper is definitional).
So every SM kernel call the deployed tx1 semantic finish executes runs on canonical
arguments (NPH_R22JoinSM4.guarded_mask_site/add_site/mul_site), on every public with the
retained digest domain. The digest-domain premise is the remaining tie: its producer at 345
(NOM_TerminalDomain.validated_digest at the installed validate's success, carried by
NOC_Stage1Forward.publicBinding) is not composed with the op10/first_decoded call that
reaches this slot. Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22JoinSM5
open Aeneas Aeneas.Std Result NNH_Run5bCtx AspisR1CurrentCaller

def Bslot (r : NP6_StdModel.Reservation) : AspisR1PublicPreparation.FinishModel.Boundaries :=
  { ClaimsUnrolledFinish.install (NP6_StdModel.calls r) (IDa_Deployed.boundaries r) with
    mask := NPH_R22JoinSM4.gmask, add := NPH_R22JoinSM4.gadd, mul := NPH_R22JoinSM4.gmul }

theorem bd_eq (r : NP6_StdModel.Reservation) :
    NPH_R22JoinSM4.Bd (NP6_StdModel.calls r) r =
      AspisR1PublicPreparation.S1SemanticRootCopy.install
        (ClaimsUnrolledFinish.install (NP6_StdModel.calls r) (IDa_Deployed.boundaries r)) := rfl
#print axioms bd_eq

theorem bg_eq (r : NP6_StdModel.Reservation) :
    NPH_R22JoinSM4.Bg (NP6_StdModel.calls r) r =
      AspisR1PublicPreparation.S1SemanticRootCopy.install (Bslot r) := rfl
#print axioms bg_eq

theorem slot_guarded {W Tx : Type} (c : Ctx W Tx) (D : aspis_core.digest.Digest32 Unit)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8)
    (hdig : LIB_VPublicDomain.publicDigestDom (FirstComposition.toRetainedPublic pub)) :
    (DrvC_Installation.currentInstalled (configuration c)).op9 D pub bytes () none =
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
        (Bslot c.fixed.reservation) D pub bytes () := by
  have h := NPH_R22JoinSM4.deployed_verify_guarded (NP6_StdModel.calls c.fixed.reservation)
    c.fixed.reservation (InstalledPreparation.retainedDigest D) (FirstComposition.toRetainedPublic pub)
    bytes () none hdig
  rw [bd_eq, bg_eq] at h
  rw [NOC_Op9Slot.slot c]
  unfold S1SemanticInstallation.verify
  rw [← h]
#print axioms slot_guarded

theorem slot_kernels (r : NP6_StdModel.Reservation) :
    (Bslot r).mask = NPH_R22JoinSM4.gmask ∧ (Bslot r).add = NPH_R22JoinSM4.gadd ∧
    (Bslot r).mul = NPH_R22JoinSM4.gmul := ⟨rfl, rfl, rfl⟩
#print axioms slot_kernels

end AspisR1.NPH_R22JoinSM5
