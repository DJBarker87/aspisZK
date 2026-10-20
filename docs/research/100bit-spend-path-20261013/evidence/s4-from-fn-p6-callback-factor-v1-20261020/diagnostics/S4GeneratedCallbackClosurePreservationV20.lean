import S4FourDotsP6ArrayOperationV1

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false

namespace AspisR1FromFnP6Generated




def packClosure (a : Aeneas.Std.Array Std.U8 608#usize)
    (b : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize) :
    fast_dots.four_dots.closure := (a, b)

private theorem pair_let_pack {T : Type}
    (a : Aeneas.Std.Array Std.U8 608#usize)
    (b : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize)
    (f : Aeneas.Std.Array Std.U8 608#usize →
      Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize → T) :
    (let (x, y) := packClosure a b; f x y) = f a b := rfl

private theorem result_bind_assoc {A B C : Type} (r : Result A)
    (f : A → Result B) (g : B → Result C) :
    (do let y ← (do let x ← r; f x); g y) =
      (do let x ← r; let y ← f x; g y) := by
  cases r <;> rfl

private theorem bind_pair_let {A B C D : Type} (z : A × B)
    (f : A → B → Result C) (g : C → Result D) :
    (do let y ← (let (a, b) := z; f a b); g y) =
      (let (a, b) := z; do let y ← f a b; g y) := by
  cases z <;> rfl

private theorem result_bind_pair_assoc {A B C D : Type}
    (r : Result (A × B)) (f : A → B → Result C) (g : C → Result D) :
    (do let y ← (do let (a, b) ← r; f a b); g y) =
      (do let (a, b) ← r; let y ← f a b; g y) := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok p => cases p <;> rfl

private theorem result_bind_congr {A B : Type} (r : Result A)
    (f g : A → Result B) (h : ∀ x, f x = g x) :
    (do let x ← r; f x) = (do let x ← r; g x) := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok x => exact h x

def prefixCore
    (ops : FourDotsOps)
    (a : Aeneas.Std.Array Std.U8 608#usize)
    (a1 : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize)
    (tupled_args : Usize) :
    Result (aspis_core.field.wide_exact.WideExact ×
      aspis_core.field.wide_exact.WideExact) :=
  have limbs := Array.repeat 8#usize 0#u64
  do
    let iter ← core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := 26#usize } 4#usize
    let limbs1 ← fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      ops iter a a1 tupled_args limbs
    let a2 ← ops.arrayFromFn 8#usize
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops) limbs1
    let o ← ops.wideFromLimbs a2
    let value ← core.option.Option.unwrap o
    let tail ← ops.ebyKNew
    let we ← Array.index_usize a1 28#usize
    let i ← tupled_args * 120#usize
    let i1 ← i + 104#usize
    let i2 ← i + 120#usize
    let s ← core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
      a { start := i1, «end» := i2 }
    let o1 ← ops.qm31FromBytes s
    let q ← core.option.Option.unwrap o1
    let (r, tail1) ← ops.ebyKPush tail we q
    core.result.Result.unwrap core.fmt.DebugUnit r
    let tail2 ← fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
      ops { start := 0#usize, «end» := 2#usize } a a1 tupled_args tail1
    let we1 ← ops.ebyKFinish tail2
    .ok (value, we1)


def actualGeneratedCallbackPrefix
    (ops : FourDotsOps) (c : fast_dots.four_dots.closure) (tupled_args : Usize) :
    Result (aspis_core.field.wide_exact.WideExact ×
      aspis_core.field.wide_exact.WideExact) :=
  let (a, a1) := c
  prefixCore ops a a1 tupled_args

def fullCore
    (ops : FourDotsOps)
    (a : Aeneas.Std.Array Std.U8 608#usize)
    (a1 : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize)
    (tupled_args : Usize) : Result (aspis_core.field.wide_exact.WideExact × fast_dots.four_dots.closure) :=
  have limbs := Array.repeat 8#usize 0#u64
  do
    let iter ← core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := 26#usize } 4#usize
    let limbs1 ← fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      ops iter a a1 tupled_args limbs
    let a2 ← ops.arrayFromFn 8#usize
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops) limbs1
    let o ← ops.wideFromLimbs a2
    let value ← core.option.Option.unwrap o
    let tail ← ops.ebyKNew
    let we ← Array.index_usize a1 28#usize
    let i ← tupled_args * 120#usize
    let i1 ← i + 104#usize
    let i2 ← i + 120#usize
    let s ← core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
      a { start := i1, «end» := i2 }
    let o1 ← ops.qm31FromBytes s
    let q ← core.option.Option.unwrap o1
    let (r, tail1) ← ops.ebyKPush tail we q
    core.result.Result.unwrap core.fmt.DebugUnit r
    let tail2 ← fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
      ops { start := 0#usize, «end» := 2#usize } a a1 tupled_args tail1
    let we1 ← ops.ebyKFinish tail2
    let we2 ← ops.wideAdd value we1
    .ok (we2, packClosure a a1)

theorem prefix_pack (ops : FourDotsOps) (a : Aeneas.Std.Array Std.U8 608#usize)
    (a1 : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize) (i : Usize) :
    actualGeneratedCallbackPrefix ops (packClosure a a1) i = prefixCore ops a a1 i := rfl

theorem full_pack (ops : FourDotsOps) (a : Aeneas.Std.Array Std.U8 608#usize)
    (a1 : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize) (i : Usize) :
    fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      ops (packClosure a a1) i = fullCore ops a a1 i := by
  unfold fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
  rfl

theorem fullCore_factor (ops : FourDotsOps) (a : Aeneas.Std.Array Std.U8 608#usize)
    (a1 : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize) (i : Usize) :
    fullCore ops a a1 i = (do
      let (value, we1) ← prefixCore ops a a1 i
      let we2 ← ops.wideAdd value we1
      .ok (we2, packClosure a a1)) := by
  simp only [fullCore, prefixCore, result_bind_assoc]
  repeat' (first | apply result_bind_congr | intro _)
  rename_i pushed
  cases pushed with
  | mk r tail1 =>
      rw [bind_pair_let]
      cases hu : core.result.Result.unwrap core.fmt.DebugUnit r with
      | fail e => simp only [hu, bind_tc_fail]
      | div => simp only [hu, bind_tc_div]
      | ok u =>
          cases hloop : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
              ops { start := 0#usize, «end» := 2#usize } a a1 i tail1 with
          | fail e => simp only [hloop, bind_tc_fail]
          | div => simp only [hloop, bind_tc_div]
          | ok tail2 =>
              cases hfinish : ops.ebyKFinish tail2 with
              | fail e => simp only [hfinish, bind_tc_fail]
              | div => simp only [hfinish, bind_tc_div]
              | ok we1 => rfl


theorem actualGeneratedCallback_factor
    (ops : FourDotsOps) (c : fast_dots.four_dots.closure) (i : Usize) :
    fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      ops c i = (do
      let (value, we1) ← actualGeneratedCallbackPrefix ops c i
      let we2 ← ops.wideAdd value we1
      .ok (Prod.mk we2 c)) := by
  cases c with
  | mk a a1 =>
      change fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        ops (packClosure a a1) i = (do
          let (value, we1) ← actualGeneratedCallbackPrefix ops (packClosure a a1) i
          let we2 ← ops.wideAdd value we1
          .ok (Prod.mk we2 (packClosure a a1)))
      rw [full_pack, prefix_pack]
      exact fullCore_factor ops a a1 i

theorem actualGeneratedCallback_success_preserves_closure
    (ops : FourDotsOps) (c : fast_dots.four_dots.closure) (i : Usize)
    {value : aspis_core.field.wide_exact.WideExact} {c' : fast_dots.four_dots.closure}
    (h : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      ops c i = .ok (value, c')) : c' = c := by
  rw [actualGeneratedCallback_factor] at h
  cases hp : actualGeneratedCallbackPrefix ops c i with
  | fail e => simp only [hp, bind_tc_fail] at h; cases h
  | div => simp only [hp, bind_tc_div] at h; cases h
  | ok pair =>
      rcases pair with ⟨v, w⟩
      simp only [hp, bind_tc_ok] at h
      change (do
        let z ← ops.wideAdd v w
        .ok (z, c)) = .ok (value, c') at h
      cases ha : ops.wideAdd v w with
      | fail e => simp only [ha, bind_tc_fail] at h; cases h
      | div => simp only [ha, bind_tc_div] at h; cases h
      | ok z =>
          simp only [ha, bind_tc_ok] at h
          have hp := Result.ok.inj h
          exact (Prod.mk.inj hp).2.symm

#print axioms actualGeneratedCallback_factor
#print axioms actualGeneratedCallback_success_preserves_closure

end AspisR1FromFnP6Generated
