import NHE_DotLoop
set_option autoImplicit false
namespace NHE_Dot
open Aeneas Aeneas.Std Result AspisR1 NHE_DotBody

def source (bytes : Slice U8) (weights : Slice NQ) : Result (core.result.Result NE NHE_DotBody.Error) := do
 let initial ← FIo_Native.fast_pairing.EbyKDot.new
 let (dot,pending) ← loop (body bytes weights) (initial,0#usize)
 match pending with
 | some r => ok r
 | none =>
  let out ← FIo_Native.fast_pairing.EbyKDot.finish dot
  ok (.Ok out)

theorem finish (d : Dot) :
 FIo_FieldBridge.map NHE_DotRead.finishE (FIo_Native.fast_pairing.EbyKDot.finish d)=
 AspisR1FinishDotSourceABI.finishFromPush (NHE_DotState.toPush d) := by
 have h := congrArg (FIo_FieldBridge.map SAG_DotAdapter.toFinishE) (NHE_DotFinish.cohort d)
 rw [NHE_DotRead.map_comp] at h
 simp only [FIo_FieldBridge.map_bind,FIo_FieldBridge.map_ok,SAG_DotAdapter.roundtrip_finishE,FIn_ExtractInstall.bind_ok] at h
 exact h

theorem cohort (bytes : Slice U8) (weights : Slice NQ) (size : weights.val.length≤64) :
 FIo_FieldBridge.map result (source bytes weights)=
 AspisR1FinishRelationCurrent.verifier.finish_query_dot ops bytes (SAG_DotAdapter.mapSlice NHE_DotRead.finishQ weights) := by
 let initial : Dot := ⟨⟨Array.repeat 4#usize 0#u64⟩,⟨Array.repeat 4#usize 0#u64⟩,0#usize⟩
 have hn : FIo_Native.fast_pairing.EbyKDot.new=ok initial := by
  simp only [FIo_Native.fast_pairing.EbyKDot.new,FIo_Native.fast_pairing.canonical.Dot.new,bind_tc_ok]
  rfl
 have hnew := NHE_DotState.new
 rw [hn] at hnew
 have hl := NHE_DotLoop.cohort bytes weights size (initial,0#usize)
 have newSlot : ops.newDot=ok (NHE_DotState.toPush initial) := hnew.symm
 unfold source AspisR1FinishRelationCurrent.verifier.finish_query_dot
 rw [newSlot]
 simp only [hn,bind_tc_ok]

 rw [←hl]
 cases run : loop (body bytes weights) (initial,0#usize) with
 | fail e => rfl
 | div => rfl
 | ok exit =>
  rcases exit with ⟨dot,pending⟩
  cases pending with
  | some r => cases r <;> rfl
  | none =>
   simp only [FIo_FieldBridge.map,bind_tc_ok,rm,Option.map_none]
   rw [←finish dot]
   cases hf : FIo_Native.fast_pairing.EbyKDot.finish dot <;> rfl

#print axioms finish
#print axioms cohort
end NHE_Dot
