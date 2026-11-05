import NHE_DotDeployed
set_option autoImplicit false
namespace NHE_DotDomain
open Aeneas Aeneas.Std Result AspisR1 NHE_DotBody

theorem push_count (before after : Dot) (value : NE) (scalar : NQ)
 (run : FIo_Native.fast_pairing.EbyKDot.push before value scalar=ok (.Ok (),after)) :
 after.count.val=before.count.val+1 := by
 have source := (NHE_PublicDot.cohort before value scalar).symm
 rw [run] at source
 change AspisR1EbyKPushDotBackend.pushWithDotBackend AspisR1EbyKPushDecodedProductUpdate.QRaw
   (NHE_DotState.toPush before) (NHE_PublicDot.toWide value) (NHE_CheckedScalar.toPush scalar)=
  ok (.Ok (),NHE_DotState.toPush after) at source
 obtain ⟨lo,hi,hlo,hhi,sl,sr,guard,count,canonical⟩ :=
  AspisR1EbyKPushDotBackend.successful_push_exact_backend _ _ _ _ _ source
 exact count

theorem step (bytes : Slice U8) (weights : Slice NQ) (size : weights.val.length≤64) (s n : State)
 (inv : s.1.count.val=s.2.val) (run : body bytes weights s=ok (.cont n)) :
 n.1.count.val=n.2.val ∧ n.2.val≤64 := by
 unfold body at run
 split at run
 · rename_i active
   obtain ⟨value,hv,rest⟩ := Port3_PushFrame.bind_success _ _ _ run
   obtain ⟨scalar,hq,rest⟩ := Port3_PushFrame.bind_success _ _ _ rest
   obtain ⟨pair,hp,rest⟩ := Port3_PushFrame.bind_success _ _ _ rest
   rcases pair with ⟨reply,dot⟩
   cases reply with
   | Err u => cases u;cases rest
   | Ok u =>
    cases u
    obtain ⟨j,hj,rest⟩ := Port3_PushFrame.bind_success _ _ _ rest
    have eq : (dot,j)=n := ControlFlow.cont.inj (Result.ok.inj rest)
    rw [←eq]
    have updated := push_count s.1 dot value scalar hp
    have index := UScalar.add_equiv s.2 1#usize
    rw [hj] at index
    have plus : j.val=s.2.val+1 := index.2.1
    change s.2.val<weights.val.length at active
    change dot.count.val=j.val ∧ j.val≤64
    constructor <;> omega
 · cases run

#print axioms push_count
#print axioms step
end NHE_DotDomain
