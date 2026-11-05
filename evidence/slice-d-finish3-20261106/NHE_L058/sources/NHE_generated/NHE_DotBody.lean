import NHE_DotRead
import NHE_LoopMap
import NHE_DotFinish
set_option autoImplicit false
namespace NHE_DotBody
open Aeneas Aeneas.Std Result ControlFlow AspisR1
abbrev Dot := NHE_DotState.Dot
abbrev NQ := NHE_CheckedScalar.NQ
abbrev NE := FIo_Install.NE
abbrev Error := AspisR1FinishRelationCurrent.verifier.Error
abbrev State := Dot × Usize
abbrev Exit := Dot × Option (core.result.Result NE Error)

def ops := AspisR1FinishDotConcreteOps.withConcreteDot
 (AspisR1CurrentWide.Proof.finishConcreteField SAG_DotClosed.seed)
 AspisR1EbyKPushDecodedProductUpdate.QRaw

def result : core.result.Result NE Error → core.result.Result AspisR1CurrentWide.Proof.FinishE Error
 | .Ok x=>.Ok (NHE_DotRead.finishE x)
 | .Err e=>.Err e

def sm (s : State) := (NHE_DotState.toPush s.1,s.2)
def rm (s : Exit) := (NHE_DotState.toPush s.1,s.2.map result)

def body (bytes : Slice U8) (weights : Slice NQ) (s : State) : Result (ControlFlow State Exit) := do
 if s.2<weights.len then
  let value ← FIo_Native.weights.field bytes s.2
  let scalar ← Slice.index_usize weights s.2
  let (r,dot) ← FIo_Native.fast_pairing.EbyKDot.push s.1 value scalar
  match r with
  | .Err () => ok (.done (dot,some (.Err .Parse)))
  | .Ok () =>
   let j ← s.2+1#usize
   ok (.cont (dot,j))
 else ok (.done (s.1,none))

theorem step (bytes : Slice U8) (weights : Slice NQ) (size : weights.val.length≤64) (s : State) :
 FIo_FieldBridge.map (NHE_LoopMap.control sm rm) (body bytes weights s)=
 AspisR1FinishRelationCurrent.verifier.finish_query_dot_loop.body ops bytes
  (SAG_DotAdapter.mapSlice NHE_DotRead.finishQ weights) (sm s).1 (sm s).2 := by
 have len : (SAG_DotAdapter.mapSlice NHE_DotRead.finishQ weights).len=weights.len := by
  apply UScalar.eq_of_val_eq
  simp only [Slice.len_val,Slice.length,SAG_DotAdapter.mapSlice,List.length_map]
 unfold body AspisR1FinishRelationCurrent.verifier.finish_query_dot_loop.body
 simp only [sm,len]
 by_cases active : s.2<weights.len
 · have small : s.2.val<64 := by have h:=active;change s.2.val<weights.val.length at h;omega
   have field := NHE_DotRead.field bytes s.2 small
   have weight := NHE_DotRead.weight weights s.2
   simp only [active,if_true,FIo_FieldBridge.map_bind,ops,AspisR1FinishDotConcreteOps.withConcreteDot,AspisR1CurrentWide.Proof.finishConcreteField,AspisR1CurrentWide.Proof.finishCheckedArithmetic,AspisR1CurrentWide.Proof.finishArithmetic]
   rw [←field,←weight]
   cases hf : FIo_Native.weights.field bytes s.2 with
   | fail e => rfl
   | div => rfl
   | ok value =>
    cases hw : Slice.index_usize weights s.2 with
    | fail e => rfl
    | div => rfl
    | ok scalar =>
     have push := NHE_PublicDot.cohort s.1 value scalar
     change FIo_FieldBridge.map NHE_PublicDot.reply (FIo_Native.fast_pairing.EbyKDot.push s.1 value scalar)=
      AspisR1EbyKPushDotBackend.pushWithDotBackend AspisR1EbyKPushDecodedProductUpdate.QRaw
       (NHE_DotState.toPush s.1)
       (AspisR1FinishDotConcreteOps.toPushWide (NHE_DotRead.finishE value))
       (AspisR1FinishDotConcreteOps.toPushQM (NHE_DotRead.finishQ scalar)) at push
     simp only [FIo_FieldBridge.map,bind_tc_ok]
     rw [←push]
     cases hp : FIo_Native.fast_pairing.EbyKDot.push s.1 value scalar with
     | fail e => rfl
     | div => rfl
     | ok pair =>
      rcases pair with ⟨r,dot⟩
      cases r with
      | Err u => cases u;rfl
      | Ok u =>
       cases u
       cases hn : s.2+1#usize <;> rfl
 · simp only [active,if_false,FIo_FieldBridge.map,NHE_LoopMap.control,rm,Option.map_none]

#print axioms step
end NHE_DotBody
