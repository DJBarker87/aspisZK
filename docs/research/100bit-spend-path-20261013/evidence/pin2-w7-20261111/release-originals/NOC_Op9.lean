import NOC_Op9Slot
import NNV_PreparedInputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_Op9
open Aeneas Aeneas.Std Result NNH_Run5bCtx

/-- X3: the first unclosed A1 association, exactly as stated in
NNV_REMAINING/NNX_REMAINING. The installed op9 slot at the host
configuration returns the SAME semantic value as the returned observed
library call; the reservation is derived from that SAME call. -/
theorem op9 {W Tx : Type} (c : Ctx W Tx) (pub : NNH_Libraries.VL.Public) (bytes : Slice U8)
 (sem : RSL.Verified NNH_Libraries.VL) :
 NNH_ObservedReturns.value ⟨pub, LIB_Carriers.bytes bytes⟩ (envOf c) = .ok sem →
 (DrvC_Installation.currentInstalled (configuration c)).op9
  (NNV_PreparedAtHost.digest c)
  (AspisR1CurrentCaller.FirstComposition.toCurrentPublic pub) bytes () none =
 .ok (.Ok (NNV_PreparedInputs.sem sem)) := by
 intro called
 obtain ⟨p, -, -, -⟩ := NNV_SemanticPrefix.returned pub bytes (envOf c) sem called
 obtain ⟨head⟩ := NNV_FinishCut.returned _ (envOf c) sem p.finished
 have hres := NOC_Op9Slot.reservation c (NNV_FinishClaims.returned _ _ _ head.claimed).1
 have vp := NOC_Op9Slot.prefix_finish pub bytes (envOf c) sem called
 rw [NOC_Op9Slot.slot c, hres]
 unfold AspisR1CurrentCaller.S1SemanticInstallation.verify
 rw [NOC_Op9Slot.pub_round, NOC_Op9Slot.digest c]
 noc_stp vp
 rfl
#print axioms op9
end AspisR1.NOC_Op9
end
