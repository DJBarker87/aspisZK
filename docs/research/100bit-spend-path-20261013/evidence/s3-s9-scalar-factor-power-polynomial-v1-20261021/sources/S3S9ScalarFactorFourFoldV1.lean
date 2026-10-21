import S3S9ScalarFactorFoldStepV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ScalarFactorFourFoldV1

abbrev Ops := AspisR1S9HelperP6.FieldOps
abbrev S := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev C := AspisR1S9HelperP6.weights.Weights.scalar_factor.closure
abbrev U := Std.Usize

def range04 : core.ops.range.Range U := { start := 0#usize, «end» := 4#usize }

private theorem rangeNext_some_exact (range : core.ops.range.Range U)
    (hlt : range.start.val < range.end.val) :
    ∃ next, AspisR1S3S9RangeFoldP6.rangeNext range =
        .ok (some range.start, next) ∧
      next.start.val = range.start.val + 1 ∧ next.end = range.end := by
  have hnextSpec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_some_spec
    (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
    (by intros; rfl) (by intros; rfl) range hlt
  obtain ⟨pair, hnext, hpost⟩ := WP.spec_imp_exists hnextSpec
  rcases pair with ⟨opt, next⟩
  rcases hpost with ⟨hopt, hstart, hend⟩
  subst opt
  exact ⟨next, hnext, hstart, hend⟩

private theorem rangeNext_none_exact (range : core.ops.range.Range U)
    (hge : range.start.val ≥ range.end.val) :
    AspisR1S3S9RangeFoldP6.rangeNext range = .ok (none, range) := by
  have hnextSpec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_none_spec
    (cloneInst := core.clone.CloneUsize)
    (partialOrdInst := core.cmp.PartialOrdUsize)
    (by intros; rfl) range hge
  obtain ⟨pair, hnext, hpost⟩ := WP.spec_imp_exists hnextSpec
  rcases pair with ⟨opt, next⟩
  rcases hpost with ⟨hopt, hiter⟩
  subst opt
  have hnextEq : next = range := hiter
  rw [hnextEq] at hnext
  simpa [AspisR1S3S9RangeFoldP6.rangeNext] using hnext

private def range1 : core.ops.range.Range U := { start := 1#usize, «end» := 4#usize }
private def range2 : core.ops.range.Range U := { start := 2#usize, «end» := 4#usize }
private def range3 : core.ops.range.Range U := { start := 3#usize, «end» := 4#usize }
private def range4 : core.ops.range.Range U := { start := 4#usize, «end» := 4#usize }

private theorem rangeNext_range04 : AspisR1S3S9RangeFoldP6.rangeNext range04 =
    .ok (some 0#usize, range1) := by
  obtain ⟨next, hnext, hstart, hend⟩ := rangeNext_some_exact range04 (by decide)
  have hs : next.start = 1#usize := Aeneas.Std.UScalar.eq_of_val_eq (by simpa [range04] using hstart)
  have he : next.end = 4#usize := by simpa [range04] using hend
  have hn : next = range1 := by
    cases next with
    | mk start stop =>
        have hs' : start = 1#usize := by simpa using hs
        have he' : stop = 4#usize := by simpa using he
        subst start
        subst stop
        rfl
  simpa [range04, hn] using hnext

private theorem rangeNext_range1 : AspisR1S3S9RangeFoldP6.rangeNext range1 =
    .ok (some 1#usize, range2) := by
  obtain ⟨next, hnext, hstart, hend⟩ := rangeNext_some_exact range1 (by decide)
  have hs : next.start = 2#usize := Aeneas.Std.UScalar.eq_of_val_eq (by simpa [range1] using hstart)
  have he : next.end = 4#usize := by simpa [range1] using hend
  have hn : next = range2 := by
    cases next with
    | mk start stop =>
        have hs' : start = 2#usize := by simpa using hs
        have he' : stop = 4#usize := by simpa using he
        subst start
        subst stop
        rfl
  simpa [range1, hn] using hnext

private theorem rangeNext_range2 : AspisR1S3S9RangeFoldP6.rangeNext range2 =
    .ok (some 2#usize, range3) := by
  obtain ⟨next, hnext, hstart, hend⟩ := rangeNext_some_exact range2 (by decide)
  have hs : next.start = 3#usize := Aeneas.Std.UScalar.eq_of_val_eq (by simpa [range2] using hstart)
  have he : next.end = 4#usize := by simpa [range2] using hend
  have hn : next = range3 := by
    cases next with
    | mk start stop =>
        have hs' : start = 3#usize := by simpa using hs
        have he' : stop = 4#usize := by simpa using he
        subst start
        subst stop
        rfl
  simpa [range2, hn] using hnext

private theorem rangeNext_range3 : AspisR1S3S9RangeFoldP6.rangeNext range3 =
    .ok (some 3#usize, range4) := by
  obtain ⟨next, hnext, hstart, hend⟩ := rangeNext_some_exact range3 (by decide)
  have hs : next.start = 4#usize := Aeneas.Std.UScalar.eq_of_val_eq (by simpa [range3] using hstart)
  have he : next.end = 4#usize := by simpa [range3] using hend
  have hn : next = range4 := by
    cases next with
    | mk start stop =>
        have hs' : start = 4#usize := by simpa using hs
        have he' : stop = 4#usize := by simpa using he
        subst start
        subst stop
        rfl
  simpa [range3, hn] using hnext

private theorem rangeNext_range4 : AspisR1S3S9RangeFoldP6.rangeNext range4 =
    .ok (none, range4) := by
  exact rangeNext_none_exact range4 (by decide)

private theorem rangeNextTrace_four :
    AspisR1S3S9RangeFoldP6.rangeNextTrace 4 range04 =
      .ok [0#usize, 1#usize, 2#usize, 3#usize] := by
  simp [AspisR1S3S9RangeFoldP6.rangeNextTrace,
    rangeNext_range04, rangeNext_range1, rangeNext_range2,
    rangeNext_range3]

def scalarStep (callback : core.ops.function.FnMut C (S × U) S) :
    (S × C) → U → Result (S × C) := fun state index => do
  let (value, closure') ← callback.call_mut state.2 (state.1, index)
  ok (value, closure')

def fourCalls (callback : core.ops.function.FnMut C (S × U) S)
    (initial : S × C) : Result (S × C) := do
  let s0 ← scalarStep callback initial 0#usize
  let s1 ← scalarStep callback s0 1#usize
  let s2 ← scalarStep callback s1 2#usize
  let s3 ← scalarStep callback s2 3#usize
  ok s3

theorem rangeFold_fourCalls (callback : core.ops.function.FnMut C (S × U) S)
    (initial : S × C) :
    AspisR1S3S9RangeFoldP6.rangeFoldRun 4 range04 (scalarStep callback) initial =
      fourCalls callback initial := by
  rw [AspisR1S3S9RangeFoldP6.rangeFoldRun_eq_foldIndices_of_trace
    4 range04 (scalarStep callback) initial
    [0#usize, 1#usize, 2#usize, 3#usize] rangeNextTrace_four]
  simp only [AspisR1S3S9RangeFoldP6.foldIndices, fourCalls]

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {z : β} (h : Bind.bind r f = .ok z) :
    ∃ x, r = .ok x ∧ f x = .ok z := by
  cases r with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem installed_scalar_call_preserves_closure
    (ops : Ops) (c : C) (arg : S × U) (z : S) (c' : C)
    (h : (letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops
      AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
        c arg) = .ok (z, c')) : c' = c := by
  cases c with
  | mk p f =>
      obtain ⟨acc, i⟩ := arg
      letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops
      have hdispatch := AspisR1S9ScalarFactorActualOpsStepV1.scalar_factor_call_mut_dispatch
        ops (p, f) (acc, i)
      rw [hdispatch] at h
      change (do
        let permIndex ← Array.index_usize AspisR1S9HelperP6.weights.PERM i
        let we ← Array.index_usize p permIndex
        let q ← Array.index_usize f i
        let we1 ← AspisR1S9GeneratedWideMulQM31V2.actualHelperOperation we q
        let we2 ← AspisR1S9CurrentFieldOpsV1.actualWideAdd acc we1
        ok (we2, (p, f))) = .ok (z, c') at h
      rcases bind_ok_inv h with ⟨permIndex, _, h⟩
      rcases bind_ok_inv h with ⟨we, _, h⟩
      rcases bind_ok_inv h with ⟨q, _, h⟩
      rcases bind_ok_inv h with ⟨we1, _, h⟩
      rcases bind_ok_inv h with ⟨we2, _, h⟩
      have hp : (we2, (p, f)) = (z, c') := Result.ok.inj h
      exact (congrArg Prod.snd hp).symm

theorem scalarStep_success_preserves_closure
    (callback : core.ops.function.FnMut C (S × U) S)
    (hpres : ∀ (acc : S) (c : C) (index : U) (z : S) (c' : C),
      callback.call_mut c (acc, index) = .ok (z, c') → c' = c)
    (acc : S) (c : C) (index : U) (z : S) (c' : C)
    (h : scalarStep callback (acc, c) index = .ok (z, c')) : c' = c := by
  unfold scalarStep at h
  rcases bind_ok_inv h with ⟨pair, hcall, hret⟩
  obtain ⟨value, closure⟩ := pair
  have heq : (value, closure) = (z, c') := Result.ok.inj hret
  have hc : closure = c' := congrArg Prod.snd heq
  have hpres' := hpres acc c index value closure hcall
  exact hc.symm.trans hpres'

theorem fourCalls_success_inv
    (callback : core.ops.function.FnMut C (S × U) S)
    (initial final : S × C)
    (h : fourCalls callback initial = .ok final) :
    ∃ s0 s1 s2 : S × C,
      scalarStep callback initial 0#usize = .ok s0 ∧
      scalarStep callback s0 1#usize = .ok s1 ∧
      scalarStep callback s1 2#usize = .ok s2 ∧
      scalarStep callback s2 3#usize = .ok final := by
  unfold fourCalls at h
  rcases bind_ok_inv h with ⟨s0, h0, hrest⟩
  rcases bind_ok_inv hrest with ⟨s1, h1, hrest⟩
  rcases bind_ok_inv hrest with ⟨s2, h2, hrest⟩
  rcases bind_ok_inv hrest with ⟨s3, h3, hlast⟩
  have heq : s3 = final := Result.ok.inj hlast
  subst final
  exact ⟨s0, s1, s2, h0, h1, h2, h3⟩

/-- The helper's successful outer result entails four exact ordered callback
transitions in the accepted range-fold model. Rust Iterator::fold correspondence
is precisely the explicit `IteratorFoldRangeP6Law` premise. -/
theorem scalar_factor_success_four_fold_calls
    (ops : Ops) (f : Array Q 4#usize) (p : Array S 4#usize) (out : S)
    (hfold : AspisR1S9HelperP6.IteratorFoldRangeP6Law
      (AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops))
    (h : (letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops
      AspisR1S9HelperP6.weights.Weights.scalar_factor f p) = .ok out) :
    (letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops;
      ∃ (we : S) (s0 s1 s2 : S × C),
      AspisR1S9CurrentFieldOpsV1.actualWideMulM31 we
          AspisR1S9HelperP6.weights.QUARTER = .ok out ∧
      scalarStep
          AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
          (AspisR1S9HelperP6.field.WideExact.ZERO, (p, f)) 0#usize = .ok s0 ∧
      scalarStep
          AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
          s0 1#usize = .ok s1 ∧
      scalarStep
          AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
          s1 2#usize = .ok s2 ∧
      scalarStep
          AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
          s2 3#usize = .ok (we, (p, f))) := by
  obtain ⟨we, hfoldRun, hmul⟩ :=
    AspisR1S9ScalarFactorActualOpsStepV1.scalar_factor_success_exposes_actual_final_mul
      ops f p out h
  letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops
  have hrange : AspisR1S9HelperP6.FieldOps.iterFold
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
      range04 AspisR1S9HelperP6.field.WideExact.ZERO (p, f) =
      AspisR1S9HelperP6.iterFoldRange
        AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
        range04 AspisR1S9HelperP6.field.WideExact.ZERO (p, f) :=
    hfold _ range04 _ _
  change AspisR1S9HelperP6.FieldOps.iterFold
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
      range04 AspisR1S9HelperP6.field.WideExact.ZERO (p, f) = .ok we at hfoldRun
  rw [hrange] at hfoldRun
  unfold AspisR1S9HelperP6.iterFoldRange at hfoldRun
  change (do
    let (value, _) ← AspisR1S3S9RangeFoldP6.rangeFoldRun 4 range04
      (scalarStep
        AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact)
      (AspisR1S9HelperP6.field.WideExact.ZERO, (p, f))
    ok value) = .ok we at hfoldRun
  rw [rangeFold_fourCalls] at hfoldRun
  rcases bind_ok_inv hfoldRun with ⟨finalState, hcalls, hvalue⟩
  let cFinal := finalState.2
  have hfinal : finalState = (we, cFinal) := by
    cases finalState with
    | mk v c =>
        simp [cFinal] at hvalue
        exact Prod.ext hvalue rfl
  have hcalls' : fourCalls
      AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
      (AspisR1S9HelperP6.field.WideExact.ZERO, (p, f)) = .ok (we, cFinal) := by
    rw [← hfinal]
    exact hcalls
  obtain ⟨s0, s1, s2, h0, h1, h2, h3⟩ :=
    fourCalls_success_inv
      AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
      (AspisR1S9HelperP6.field.WideExact.ZERO, (p, f)) (we, cFinal) hcalls'
  letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops
  let callback :=
    AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
  have hpres : ∀ (acc : S) (c : C) (index : U) (z : S) (c' : C),
      callback.call_mut c (acc, index) = .ok (z, c') → c' = c := by
    intro acc c index z c' hcall
    exact installed_scalar_call_preserves_closure ops c (acc, index) z c' hcall
  have hc0 : s0.2 = (p, f) := scalarStep_success_preserves_closure
      callback hpres AspisR1S9HelperP6.field.WideExact.ZERO (p, f) 0#usize s0.1 s0.2 h0
  have hc1 : s1.2 = s0.2 := scalarStep_success_preserves_closure
      callback hpres s0.1 s0.2 1#usize s1.1 s1.2 h1
  have hc2 : s2.2 = s1.2 := scalarStep_success_preserves_closure
      callback hpres s1.1 s1.2 2#usize s2.1 s2.2 h2
  have hc3 : cFinal = s2.2 := scalarStep_success_preserves_closure
      callback hpres s2.1 s2.2 3#usize we cFinal h3
  have hcFinal : cFinal = (p, f) := by rw [hc3, hc2, hc1, hc0]
  rw [hcFinal] at h3
  exact ⟨we, s0, s1, s2, hmul, h0, h1, h2, h3⟩

end AspisR1S9ScalarFactorFourFoldV1
