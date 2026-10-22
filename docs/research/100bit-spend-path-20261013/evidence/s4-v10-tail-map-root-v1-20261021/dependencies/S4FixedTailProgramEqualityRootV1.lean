import S4TailLiteralEqualityRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsFixedTailProgramEqualityRootV1
open AspisR1FastDotsActualCallbackTailTraceRootV1 (Ops Wide)
open AspisR1FastDotsTailLiteralEqualityRootV1 (literalPush literalTwoPushes actual_tail_eq_literal_two_pushes)
open AspisR1FastDotsCurrent

def oldTail (ops : Ops) (a : Array Std.U8 608#usize) (a1 : Array Wide 29#usize)
    (slot : Usize) (value : Wide) : Result Wide := do
  let tail ← ops.ebyKNew
  let we ← Array.index_usize a1 28#usize
  let i ← slot * 120#usize
  let i1 ← i + 104#usize
  let i2 ← i + 120#usize
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a
      { start := i1, «end» := i2 }
  let o1 ← ops.qm31FromBytes s
  let q ← core.option.Option.unwrap o1
  let (r, tail1) ← ops.ebyKPush tail we q
  core.result.Result.unwrap core.fmt.DebugUnit r
  let tail2 ←
    fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1 ops
      { start := 0#usize, «end» := 2#usize } a a1 slot tail1
  let we1 ← ops.ebyKFinish tail2
  let we2 ← ops.wideAdd value we1
  ok we2

def fixedTail (ops : Ops) (a : Array Std.U8 608#usize) (a1 : Array Wide 29#usize)
    (slot : Usize) (value : Wide) : Result Wide := do
  let tail ← ops.ebyKNew
  let we ← Array.index_usize a1 28#usize
  let i8 ← slot * 120#usize
  let i9 ← i8 + 104#usize
  let i10 ← i8 + 120#usize
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a
      { start := i9, «end» := i10 }
  let o1 ← ops.qm31FromBytes s
  let q1 ← core.option.Option.unwrap o1
  let (r, tail1) ← ops.ebyKPush tail we q1
  core.result.Result.unwrap core.fmt.DebugUnit r
  let i11 ← slot * 32#usize
  let i12 ← 480#usize + i11
  let i13 ← 0#usize * 16#usize
  let offset0 ← i12 + i13
  let i14 ← 0#usize + 26#usize
  let we1 ← Array.index_usize a1 i14
  let i15 ← offset0 + 16#usize
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a
      { start := offset0, «end» := i15 }
  let o2 ← ops.qm31FromBytes s1
  let q2 ← core.option.Option.unwrap o2
  let (r1, tail2) ← ops.ebyKPush tail1 we1 q2
  core.result.Result.unwrap core.fmt.DebugUnit r1
  let i16 ← 480#usize + i11
  let i17 ← 1#usize * 16#usize
  let offset1 ← i16 + i17
  let i18 ← 1#usize + 26#usize
  let we2 ← Array.index_usize a1 i18
  let i19 ← offset1 + 16#usize
  let s2 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a
      { start := offset1, «end» := i19 }
  let o3 ← ops.qm31FromBytes s2
  let q3 ← core.option.Option.unwrap o3
  let (r2, tail3) ← ops.ebyKPush tail2 we2 q3
  core.result.Result.unwrap core.fmt.DebugUnit r2
  let we3 ← ops.ebyKFinish tail3
  ops.wideAdd value we3

private theorem result_bind_assoc {α β γ : Type} (r : Result α)
    (f : α → Result β) (g : β → Result γ) :
    ((r >>= f) >>= g)=(r >>= fun x => f x >>= g) := by cases r <;> rfl
private theorem result_bind_ok_id {α : Type} (r : Result α) :
    (r >>= fun x => .ok x)=r := by cases r <;> rfl

private theorem bind_congr_right {A B : Type} (r : Result A)
    (f g : A → Result B) (h : ∀ x, f x=g x) : (r >>= f)=(r >>= g) := by
  cases r with
  | ok x => exact h x
  | fail e => rfl
  | div => rfl

/-- The exact selected fixed-helper tail program and original callback tail
program have identical Result outcomes. Repeated slot arithmetic is pure and
identified by its same result; no source/parser/push success is assumed. -/
theorem fixed_tail_eq_old_tail
    (ops : Ops) (a : Array Std.U8 608#usize) (a1 : Array Wide 29#usize)
    (slot : Usize) (value : Wide) :
    fixedTail ops a a1 slot value=oldTail ops a a1 slot value := by
  have heq (tail : fast_pairing.EbyKDot) :
      fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
        ops {start:=0#usize,«end»:=2#usize} a a1 slot tail=
      literalTwoPushes ops a a1 slot tail := actual_tail_eq_literal_two_pushes ops a a1 slot tail
  unfold fixedTail oldTail
  simp only [heq]
  unfold literalTwoPushes literalPush
  cases hs : slot * 32#usize <;>
    simp only [hs, bind_tc_ok, bind_tc_fail, bind_tc_div,
      result_bind_assoc, result_bind_ok_id]

  all_goals
    repeat' (apply bind_congr_right; intro x)
    rcases x with ⟨r0, t0⟩
    change (core.result.Result.unwrap core.fmt.DebugUnit r0 >>= _) =
      ((core.result.Result.unwrap core.fmt.DebugUnit r0 >>= fun _ => .ok t0) >>= _)
    rw [result_bind_assoc]
    simp only [bind_tc_ok]
    repeat' (apply bind_congr_right; intro y)
    rcases y with ⟨r1, t1⟩
    change (core.result.Result.unwrap core.fmt.DebugUnit r1 >>= _) =
      ((core.result.Result.unwrap core.fmt.DebugUnit r1 >>= fun _ => .ok t1) >>= _)
    rw [result_bind_assoc]
    simp only [bind_tc_ok]

#print axioms fixed_tail_eq_old_tail
end AspisR1FastDotsFixedTailProgramEqualityRootV1
