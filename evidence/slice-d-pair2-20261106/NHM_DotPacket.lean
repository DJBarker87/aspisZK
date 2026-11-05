import NHE_DotDomain
set_option autoImplicit false
namespace NHM_DotPacket
open Aeneas Aeneas.Std Result AspisR1
abbrev Dot := NHE_DotState.Dot
abbrev NE := FIo_Install.NE
abbrev NQ := NHE_CheckedScalar.NQ
abbrev Push := NHE_DotState.Push

def back (p : core.result.Result Unit Unit × Push) :=
 (p.1,NHE_DotState.fromPush p.2)

def push (d : Dot) (x : NE) (q : NQ) :=
 FIo_FieldBridge.map back
  (AspisR1EbyKPushDotBackend.pushWithDotBackend AspisR1EbyKPushDecodedProductUpdate.QRaw
   (NHE_DotState.toPush d) (NHE_PublicDot.toWide x) (NHE_CheckedScalar.toPush q))

theorem reply_back (p : core.result.Result Unit Unit × Dot) :
 back (NHE_PublicDot.reply p)=p := by
 rcases p with ⟨r,d⟩
 simp only [back,NHE_PublicDot.reply,NHE_DotState.from_to]

theorem source (d : Dot) (x : NE) (q : NQ) :
 FIo_Native.fast_pairing.EbyKDot.push d x q=push d x q := by
 unfold push
 rw [←NHE_PublicDot.cohort]
 rw [NHE_DotRead.map_comp]
 cases h : FIo_Native.fast_pairing.EbyKDot.push d x q with
 | fail e => rfl
 | div => rfl
 | ok p => simp only [FIo_FieldBridge.map,bind_tc_ok,reply_back]

/-- Exact post-count follows the packet's actual successful arm, not an assumed reply. -/
theorem count (d after : Dot) (x : NE) (q : NQ)
 (run : push d x q=ok (.Ok (),after)) : after.count.val=d.count.val+1 := by
 rw [←source] at run
 exact NHE_DotDomain.push_count d after x q run

#print axioms reply_back
#print axioms source
#print axioms count
end NHM_DotPacket
