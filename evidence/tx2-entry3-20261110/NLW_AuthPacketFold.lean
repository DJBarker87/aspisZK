import NLW_AuthFold
set_option autoImplicit false
noncomputable section
namespace NLW_AuthPacketFold
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLM_PacketTypes NLW_AuthState
/-- SAME-child reference. No output or independently chosen post-frame is
supplied by the caller. -/
def reference {Ambient : Type} (wr rr : NP6_StdModel.Reservation)
 (merkle : NJJ_Common.Merkle) (finish : NJJ_Common.Finish) : Child Ambient :=
 fun f world=>⟨world,NJU_CommonObserved.run wr rr merkle finish f.digest
  f.publicBytes f.proof f.checkpoint f.hash none⟩
/-- Parameterized SOURCE-projection fold; never a row root. The unproved child
packet and own-input Root0 are visible. Native segment installation pending. -/
theorem parameterized {Ambient H : Type} (child : Child Ambient)
 (wr rr : NP6_StdModel.Reservation) (merkle : NJJ_Common.Merkle) (finish : NJJ_Common.Finish)
 (packet : SourceSpec_065 child wr rr merkle finish) (s : State Ambient H)
 (publicBound : s.args.publicBytes.val.length≤1880)
 (roots : NLW_Root0.Binds s.args.checkpoint s.args.proof) :
 NLW_AuthSegments.fold child s =
 NLW_AuthState.transcription (reference wr rr merkle finish) s := by
 rw [NLW_AuthFold.transcription]
 unfold NLW_AuthState.transcription
 cases p : NLE_ParseInstall.parse s.args.proof with
 | fail err => rfl
 | div => rfl
 | ok reply =>
   cases reply with
   | Err err => rfl
   | Ok v =>
     have same := (packet s.args s.world (NLW_AuthFold.common_domain s v p publicBound roots)).1
     dsimp only at same ⊢
     rw [same]
     rfl
#print parameterized
#print axioms parameterized
end NLW_AuthPacketFold
