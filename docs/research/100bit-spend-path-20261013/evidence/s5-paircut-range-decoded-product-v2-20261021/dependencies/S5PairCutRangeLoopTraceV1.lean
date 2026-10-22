import S5PairCutRangeIterationV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1S5PairCutRangeLoopTraceV1

open AspisR1S5PairCutLoopFoldV1
open AspisR1S5PairCutRangeIterationV1
open AspisR1S5EbyKConcreteOpsInstanceV1
open AspisR1WeightsPairCutEbyKDotOpsV1

local instance installedOps : AspisR1WeightsPairCut.fast_pairing.EbyKDotOps :=
  sourceOps

abbrev PairDot := AspisR1WeightsPairCut.fast_pairing.EbyKDot
abbrev Range := core.ops.range.Range Usize
abbrev Output := (core.result.Result Unit AspisR1WeightsPairCut.verifier.Error) × PairDot

def body (read : Slice U8 → Usize → Result PairWide)
    (bytes : Slice U8) (scratch : Slice PairQM) :
    (Range × PairDot) → Result (Aeneas.Std.ControlFlow (Range × PairDot) Output) :=
  fun s => do
    let cf ← pushByteProductsBodyWith
      (core.iter.range.IteratorRange.next core.iter.range.StepUsize)
      read bytes scratch s.1 s.2
    match cf with
    | core.ops.control_flow.ControlFlow.Break out => .ok (.done out)
    | core.ops.control_flow.ControlFlow.Continue state => .ok (.cont state)

def run (read : Slice U8 → Usize → Result PairWide)
    (bytes : Slice U8) (scratch : Slice PairQM)
    (iter : Range) (pair : PairDot) : Result Output :=
  Aeneas.Std.loop (body read bytes scratch) (iter, pair)

private theorem body_loop_done_inv
    (read : Slice U8 → Usize → Result PairWide)
    (bytes : Slice U8) (scratch : Slice PairQM) (iter : Range)
    (pair : PairDot) (out : Output)
    (h : body read bytes scratch (iter, pair) = .ok (.done out)) :
    pushByteProductsBodyWith
      (core.iter.range.IteratorRange.next core.iter.range.StepUsize)
      read bytes scratch iter pair = .ok (.Break out) := by
  unfold body at h
  cases hr : pushByteProductsBodyWith
      (core.iter.range.IteratorRange.next core.iter.range.StepUsize)
      read bytes scratch iter pair with
  | fail e => simp [hr] at h
  | div => simp [hr] at h
  | ok cf =>
    cases cf with
    | Break result => simpa [hr] using h
    | Continue state => simp [hr] at h

private theorem body_loop_cont_inv
    (read : Slice U8 → Usize → Result PairWide)
    (bytes : Slice U8) (scratch : Slice PairQM) (iter : Range)
    (pair : PairDot) (state : Range × PairDot)
    (h : body read bytes scratch (iter, pair) = .ok (.cont state)) :
    pushByteProductsBodyWith
      (core.iter.range.IteratorRange.next core.iter.range.StepUsize)
      read bytes scratch iter pair = .ok (.Continue state) := by
  unfold body at h
  cases hr : pushByteProductsBodyWith
      (core.iter.range.IteratorRange.next core.iter.range.StepUsize)
      read bytes scratch iter pair with
  | fail e => simp [hr] at h
  | div => simp [hr] at h
  | ok cf =>
    cases cf with
    | Break result => simp [hr] at h
    | Continue state' => simpa [hr] using h

inductive CallbackRangeTrace (read : Slice U8 → Usize → Result PairWide)
    (bytes : Slice U8) (scratch : Slice PairQM) (n : Usize) :
    Range → PairDot → List Usize → PairDot → Prop where
  | done {out : PairDot} (iter : Range) (pair : PairDot)
      (hend : iter.end.val = n.val)
      (hat : iter.start.val = n.val) (hout : pair = out) :
      CallbackRangeTrace read bytes scratch n iter pair [] out
  | step {iter iter' : Range} {pair pair' out : PairDot}
      {j : Usize} {js : List Usize} {value : PairWide} {scalar : PairQM}
      (hend : iter.end.val = n.val)
      (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some j, iter'))
      (hread : read bytes j = .ok value)
      (hscalar : Slice.index_usize scratch j = .ok scalar)
      (hpush : AspisR1WeightsPairCut.fast_pairing.EbyKDot.push
        pair value scalar = .ok (.Ok (), pair'))
      (htail : CallbackRangeTrace read bytes scratch n iter' pair' js out) :
      CallbackRangeTrace read bytes scratch n iter pair (j :: js) out

private theorem loop_success_cases {α β : Type}
    (step : α → Result (ControlFlow α β)) (state : α) (out : β)
    (h : Aeneas.Std.loop step state = .ok out) :
    step state = .ok (.done out) ∨
      ∃ stateNext, step state = .ok (.cont stateNext) ∧
        Aeneas.Std.loop step stateNext = .ok out := by
  rw [Aeneas.Std.loop.eq_def] at h
  cases hs : step state with
  | fail e => simp [hs] at h
  | div => simp [hs] at h
  | ok cf =>
    cases cf with
    | done result => simp [hs] at h; subst result; exact Or.inl rfl
    | cont stateNext => simp [hs] at h; exact Or.inr ⟨stateNext, rfl, h⟩

private theorem next_some_shape (iter iter' : Range) (point : Usize)
    (h : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some point, iter')) :
    point = iter.start ∧ iter.start.val < iter.end.val ∧
      iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end := by
  have hs := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
    (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
    (by intros; rfl) (by intros; rfl) iter
  rw [h, WP.spec_ok] at hs
  by_cases hlt : iter.start.val < iter.end.val
  · simp only [hlt, ↓reduceIte] at hs
    rcases hs with ⟨⟨hopt, hstart⟩, hend⟩
    exact ⟨Option.some.inj hopt, hlt, hstart, hend⟩
  · simp only [hlt, ↓reduceIte] at hs
    rcases hs with ⟨⟨hopt, _⟩, _⟩
    cases hopt

private theorem next_none_shape (iter iter' : Range)
    (h : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (none, iter')) : iter.end.val ≤ iter.start.val := by
  have hs := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
    (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
    (by intros; rfl) (by intros; rfl) iter
  rw [h, WP.spec_ok] at hs
  by_cases hlt : iter.start.val < iter.end.val
  · simp only [hlt, ↓reduceIte] at hs
    rcases hs with ⟨⟨hopt, _⟩, _⟩
    cases hopt
  · omega

private theorem body_continue_inv
    (read : Slice U8 → Usize → Result PairWide)
    (bytes : Slice U8) (scratch : Slice PairQM) (iter iter1 : Range)
    (pair pair1 : PairDot)
    (hbody : pushByteProductsBodyWith
      (core.iter.range.IteratorRange.next core.iter.range.StepUsize)
      read bytes scratch iter pair = .ok (.Continue (iter1, pair1))) :
    ∃ j value scalar,
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some j, iter1) ∧
      read bytes j = .ok value ∧ Slice.index_usize scratch j = .ok scalar ∧
      AspisR1WeightsPairCut.fast_pairing.EbyKDot.push pair value scalar =
        .ok (.Ok (), pair1) := by
  cases hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
  | fail e => simp [pushByteProductsBodyWith, hn] at hbody
  | div => simp [pushByteProductsBodyWith, hn] at hbody
  | ok p =>
    rcases p with ⟨o, iterN⟩
    cases o with
    | none => simp [pushByteProductsBodyWith, hn] at hbody
    | some j =>
      cases hr : read bytes j with
      | fail e => simp [pushByteProductsBodyWith, pushByteProductsAfterNextAt,
          pushByteProductsPostPush, hn, hr] at hbody
      | div => simp [pushByteProductsBodyWith, pushByteProductsAfterNextAt,
          pushByteProductsPostPush, hn, hr] at hbody
      | ok value =>
        cases hs : Slice.index_usize scratch j with
        | fail e => simp [pushByteProductsBodyWith, pushByteProductsAfterNextAt,
            pushByteProductsPostPush, hn, hr, hs] at hbody
        | div => simp [pushByteProductsBodyWith, pushByteProductsAfterNextAt,
            pushByteProductsPostPush, hn, hr, hs] at hbody
        | ok scalar =>
          cases hp : AspisR1WeightsPairCut.fast_pairing.EbyKDot.push
              pair value scalar with
          | fail e => simp [pushByteProductsBodyWith, hn, hr, hs, hp,
              pushByteProductsAfterNextAt, pushByteProductsPostPush] at hbody
          | div => simp [pushByteProductsBodyWith, hn, hr, hs, hp,
              pushByteProductsAfterNextAt, pushByteProductsPostPush] at hbody
          | ok result =>
            rcases result with ⟨r, pairN⟩
            cases r with
            | Err e => simp [pushByteProductsBodyWith, hn, hr, hs, hp,
                pushByteProductsAfterNextAt, pushByteProductsPostPush] at hbody
            | Ok u =>
              cases u
              have heq : iterN = iter1 ∧ pairN = pair1 := by
                simpa [pushByteProductsBodyWith, hn, hr, hs, hp,
                  pushByteProductsAfterNextAt, pushByteProductsPostPush] using hbody
              rcases heq with ⟨hiter, hpair⟩
              subst iterN
              subst pairN
              exact ⟨j, value, scalar, by simpa using hn, hr, hs, hp⟩

private theorem body_done_inv
    (read : Slice U8 → Usize → Result PairWide)
    (bytes : Slice U8) (scratch : Slice PairQM) (iter : Range)
    (pair out : PairDot)
    (hbody : pushByteProductsBodyWith
      (core.iter.range.IteratorRange.next core.iter.range.StepUsize)
      read bytes scratch iter pair = .ok (.Break (.Ok (), out))) :
    ∃ it, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (none, it) ∧ pair = out := by
  cases hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
  | fail e => simp [pushByteProductsBodyWith, hn] at hbody
  | div => simp [pushByteProductsBodyWith, hn] at hbody
  | ok p =>
    rcases p with ⟨o, it⟩
    cases o with
    | some j =>
      cases hr : read bytes j with
      | fail e => simp [pushByteProductsBodyWith, pushByteProductsAfterNextAt,
          pushByteProductsPostPush, hn, hr] at hbody
      | div => simp [pushByteProductsBodyWith, pushByteProductsAfterNextAt,
          pushByteProductsPostPush, hn, hr] at hbody
      | ok value =>
        cases hs : Slice.index_usize scratch j with
        | fail e => simp [pushByteProductsBodyWith, pushByteProductsAfterNextAt,
            pushByteProductsPostPush, hn, hr, hs] at hbody
        | div => simp [pushByteProductsBodyWith, pushByteProductsAfterNextAt,
            pushByteProductsPostPush, hn, hr, hs] at hbody
        | ok scalar =>
          cases hp : AspisR1WeightsPairCut.fast_pairing.EbyKDot.push
              pair value scalar with
          | fail e => simp [pushByteProductsBodyWith, pushByteProductsAfterNextAt,
              pushByteProductsPostPush, hn, hr, hs, hp] at hbody
          | div => simp [pushByteProductsBodyWith, pushByteProductsAfterNextAt,
              pushByteProductsPostPush, hn, hr, hs, hp] at hbody
          | ok result =>
            rcases result with ⟨r, pairN⟩
            cases r with
            | Err e => simp [pushByteProductsBodyWith, pushByteProductsAfterNextAt,
                pushByteProductsPostPush, hn, hr, hs, hp] at hbody
            | Ok u => cases u; simp [pushByteProductsBodyWith,
                pushByteProductsAfterNextAt, pushByteProductsPostPush,
                hn, hr, hs, hp] at hbody
    | none =>
      have heq : pair = out := by
        simpa [pushByteProductsBodyWith, hn] using hbody
      exact ⟨it, rfl, heq⟩

/-- A successful range loop over the source-shaped callback body has an exact
ordered trace of successful reads, scratch lookups, and EbyK pushes.  The
reader remains explicit so the external PairCut `weights.field` symbol is not
mistaken for a proved standard-library binding. -/
theorem successful_run_has_trace
    (read : Slice U8 → Usize → Result PairWide)
    (bytes : Slice U8) (scratch : Slice PairQM)
    (n : Usize) (iter : Range) (pair out : PairDot)
    (hend : iter.end.val = n.val)
    (hstart : iter.start.val ≤ n.val)
    (hrun : run read bytes scratch iter pair = .ok (.Ok (), out)) :
    ∃ js, CallbackRangeTrace read bytes scratch n iter pair js out ∧
      js.length = n.val - iter.start.val := by
  let step := body read bytes scratch
  have hloop : Aeneas.Std.loop step (iter, pair) = .ok (.Ok (), out) := hrun
  induction hfuel : n.val - iter.start.val generalizing iter pair with
  | zero =>
      have hat : iter.start.val = n.val := by omega
      rcases loop_success_cases step (iter, pair) (.Ok (), out) hloop with
        hdone | ⟨stateNext, hcont, htail⟩
      · have hbodyStd : body read bytes scratch (iter, pair) = .ok (.done (.Ok (), out)) := hdone
        have hraw := body_loop_done_inv read bytes scratch iter pair (.Ok (), out) hbodyStd
        have hbody : pushByteProductsBodyWith
          (core.iter.range.IteratorRange.next core.iter.range.StepUsize)
          read bytes scratch iter pair = .ok (.Break (.Ok (), out)) := hraw
        obtain ⟨_, hnext, hout⟩ := body_done_inv read bytes scratch iter pair out hbody
        exact ⟨[], CallbackRangeTrace.done iter pair hend hat hout, by simp⟩
      · rcases stateNext with ⟨iter', pair'⟩
        have hbodyStd : body read bytes scratch (iter, pair) = .ok (.cont (iter', pair')) := hcont
        have hbody := body_loop_cont_inv read bytes scratch iter pair (iter', pair') hbodyStd
        obtain ⟨j, _, _, hnext, _, _, _⟩ :=
          body_continue_inv read bytes scratch iter iter' pair pair' hbody
        have ⟨_, hactive, _, _⟩ := next_some_shape iter iter' j hnext
        omega
  | succ fuel ih =>
      rcases loop_success_cases step (iter, pair) (.Ok (), out) hloop with
        hdone | ⟨stateNext, hcont, htail⟩
      · have hbodyStd : body read bytes scratch (iter, pair) = .ok (.done (.Ok (), out)) := hdone
        have hraw := body_loop_done_inv read bytes scratch iter pair (.Ok (), out) hbodyStd
        have hbody : pushByteProductsBodyWith
          (core.iter.range.IteratorRange.next core.iter.range.StepUsize)
          read bytes scratch iter pair = .ok (.Break (.Ok (), out)) := hraw
        obtain ⟨it, hnext, hout⟩ := body_done_inv read bytes scratch iter pair out hbody
        have hbound := next_none_shape iter it hnext
        have hat : iter.start.val = n.val := by omega
        exact ⟨[], CallbackRangeTrace.done iter pair hend hat hout, by omega⟩
      · rcases stateNext with ⟨iter', pair'⟩
        have hbodyStd : body read bytes scratch (iter, pair) = .ok (.cont (iter', pair')) := hcont
        have hbody := body_loop_cont_inv read bytes scratch iter pair (iter', pair') hbodyStd
        obtain ⟨j, value, scalar, hnext, hread, hscalar, hpush⟩ :=
          body_continue_inv read bytes scratch iter iter' pair pair' hbody
        have ⟨hpoint, hactive, hstart', hend'⟩ := next_some_shape iter iter' j hnext
        have htail' : run read bytes scratch iter' pair' = .ok (.Ok (), out) := htail
        have hfuel' : n.val - iter'.start.val = fuel := by omega
        have hend1 : iter'.end.val = n.val := by rw [hend']; exact hend
        have hloopNext : Aeneas.Std.loop step (iter', pair') = .ok (.Ok (), out) := htail
        have htraceTail := ih iter' pair' hend1 (by omega) htail' hloopNext hfuel'
        obtain ⟨js, htrace, hlen⟩ := htraceTail
        refine ⟨j :: js, ?_, ?_⟩
        · exact CallbackRangeTrace.step hend hnext hread hscalar hpush htrace
        · simp only [List.length_cons]; omega

end AspisR1S5PairCutRangeLoopTraceV1
