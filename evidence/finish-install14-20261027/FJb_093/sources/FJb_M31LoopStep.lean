import FJb_M31Step
import FJb_PairBind
import FJb_PairProjection
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_M31LoopStep
open Aeneas Aeneas.Std Result FIq_Native
open FJb_MatrixGroupStep (State)
open FJb_M31Step (Constants)
open FIv_NativeArithmetic (NQ)
abbrev Range := core.ops.range.Range Usize
def loop (packed : Bool) (iter : Range) (a : Constants) (s : State) : Result State :=
  if packed then state_only_poseidon.full_round_m31_constants_packed_loop iter s a
  else state_only_poseidon.full_round_m31_constants_loop iter s a

theorem unfold_loop (packed : Bool) (iter : Range) (a : Constants) (s : State) :
    loop packed iter a s=(do
      let (o,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => ok s
      | some i =>
        let next ← FJb_M31Step.step s a i
        loop packed iter1 a next) := by
  cases packed with
  | false =>
    simp only [loop,Bool.false_eq_true,↓reduceIte]
    rw [state_only_poseidon.full_round_m31_constants_loop.eq_def]
    simp only [FJb_M31Step.step,FJb_M31Scalar.updated,bind_assoc_eq]
    apply congrArg (fun f : (Option Usize×Range) → Result State=>
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter >>= f)
    funext p
    rcases p with ⟨o,iter1⟩
    cases o with
    | none => rfl
    | some i =>
      apply congrArg (fun f : NQ → Result State=>Array.index_usize s i >>= f)
      funext x
      apply congrArg (fun f : U32 → Result State=>Array.index_usize a i >>= f)
      funext c
      apply congrArg (fun f : U32 → Result State=>field.M31.add x.c0.a c >>= f)
      funext m
      apply congrArg (fun f : (NQ×(NQ → State)) → Result State=>Array.index_mut_usize s i >>= f)
      funext p
      rcases p with ⟨x1,back⟩
      rfl

  | true =>
    simp only [loop,↓reduceIte]
    rw [state_only_poseidon.full_round_m31_constants_packed_loop.eq_def]
    simp only [FJb_M31Step.step,FJb_M31Scalar.updated,bind_assoc_eq]
    apply congrArg (fun f : (Option Usize×Range) → Result State=>
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter >>= f)
    funext p
    rcases p with ⟨o,iter1⟩
    cases o with
    | none => rfl
    | some i =>
      apply congrArg (fun f : NQ → Result State=>Array.index_usize s i >>= f)
      funext x
      apply congrArg (fun f : U32 → Result State=>Array.index_usize a i >>= f)
      funext c
      apply congrArg (fun f : U32 → Result State=>field.M31.add x.c0.a c >>= f)
      funext m
      apply congrArg (fun f : (NQ×(NQ → State)) → Result State=>Array.index_mut_usize s i >>= f)
      funext p
      rcases p with ⟨x1,back⟩
      rfl

#print axioms unfold_loop
end AspisR1.FJb_M31LoopStep
end
