import NewOuterLimbLoopSegmentV1
import Aeneas.Std.RangeIter

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsOldLimbLoopReverseV1

abbrev Usize := Std.Usize
abbrev U64 := UScalar UScalarTy.U64
abbrev Range := core.ops.range.Range Usize
abbrev Ops := AspisR1FastDotsNewOuterLimbLoopSegmentV1.Ops
abbrev LimbBody := AspisR1FastDotsNewOuterLimbLoopSegmentV1.LimbBody
abbrev LimbLoop := AspisR1FastDotsNewOuterLimbLoopSegmentV1.LimbLoop
open AspisR1FastDotsNewOuterLimbLoopSegmentV1 (foldSegment)

inductive FoldTrace (sums : Array U64 8#usize) : Range → Array U64 8#usize → Array U64 8#usize → Type where
  | step {iter iter' : Range} {initial mid final : Array U64 8#usize}
      (hlt : iter.start.val < iter.end.val)
      (hstart : iter'.start.val = iter.start.val + 1)
      (hend : iter'.end = iter.end)
      (hfold : foldSegment sums initial iter.start = .ok mid)
      (tail : FoldTrace sums iter' mid final) : FoldTrace sums iter initial final
  | finish {iter : Range} {initial final : Array U64 8#usize}
      (hge : iter.start.val ≥ iter.end.val) (heq : final = initial) :
      FoldTrace sums iter initial final

def FoldTrace.length {sums : Array U64 8#usize} {iter : Range}
    {initial final : Array U64 8#usize} : FoldTrace sums iter initial final → Nat
  | .step _ _ _ _ tail => tail.length + 1
  | .finish _ _ => 0

theorem FoldTrace.length_eq_remaining {sums : Array U64 8#usize}
    {iter : Range} {initial final : Array U64 8#usize}
    (trace : FoldTrace sums iter initial final) :
    trace.length = iter.end.val - iter.start.val := by
  induction trace with
  | finish hge heq => simp [FoldTrace.length, Nat.sub_eq_zero_of_le hge]
  | @step iter iter' initial mid final hlt hstart hend hfold tail ih =>
    simp only [FoldTrace.length, ih]
    rw [hstart, hend]
    omega

theorem range_next_some_success (iter : Range) (hlt : iter.start.val < iter.end.val) :
    ∃ iter',
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some iter.start, iter') ∧
      iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end := by
  have hclone : ∀ x : Usize, core.clone.CloneUsize.clone x = .ok x := by
    intro x; rfl
  have hltSpec : ∀ x y : Usize,
      core.cmp.PartialOrdUsize.lt x y = .ok (decide (x.val < y.val)) := by
    intros; rfl
  have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
    (cloneInst := core.clone.CloneUsize)
    (partialOrdInst := core.cmp.PartialOrdUsize) hclone hltSpec iter
  obtain ⟨out, hrun, hproperty⟩ := WP.spec_imp_exists hspec
  rcases out with ⟨o, iter'⟩
  simp only [hlt, ↓reduceIte] at hproperty
  rcases hproperty with ⟨⟨hopt, hadvance⟩, hend⟩
  have hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some iter.start, iter') := by rw [hrun, hopt]
  exact ⟨iter', hnext, hadvance, hend⟩

private theorem range_next_none_success (iter : Range)
    (hge : iter.start.val ≥ iter.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (none, iter) := by
  have hclone : ∀ x : Usize, core.clone.CloneUsize.clone x = .ok x := by
    intro x; rfl
  have hltSpec : ∀ x y : Usize,
      core.cmp.PartialOrdUsize.lt x y = .ok (decide (x.val < y.val)) := by
    intros; rfl
  have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
    (cloneInst := core.clone.CloneUsize)
    (partialOrdInst := core.cmp.PartialOrdUsize) hclone hltSpec iter
  obtain ⟨out, hrun, hproperty⟩ := WP.spec_imp_exists hspec
  rcases out with ⟨option, iter'⟩
  have hn : ¬ iter.start.val < iter.end.val := by omega
  simp only [hn, ↓reduceIte] at hproperty
  rcases hproperty with ⟨⟨hnone, hstart⟩, hend⟩
  have hsame : iter' = iter := by
    cases iter with
    | mk start stop =>
      cases iter' with
      | mk start' stop' =>
        have hs : start' = start := hstart
        have he : stop' = stop := hend
        subst start'; subst stop'; rfl
  have hnext : core.iter.range.IteratorRange.next
      (core.iter.range.UScalarStep UScalarTy.Usize core.clone.CloneUsize
        core.cmp.PartialOrdUsize) iter = .ok (none, iter) := by
    rw [hrun, hnone, hsame]
  simpa only [core.iter.range.StepUsize] using hnext

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

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
  | ok flow =>
    cases flow with
    | done result =>
      simp only [hs, bind_tc_ok] at h
      have heq : result = out := Result.ok.inj h
      subst result
      exact Or.inl rfl
    | cont next =>
      simp only [hs, bind_tc_ok] at h
      exact Or.inr ⟨next, rfl, h⟩

private theorem limb_body_done_range
    (ops : Ops) (sums : Array U64 8#usize) (iter : Range)
    (limbs out : Array U64 8#usize)
    (hbody : LimbBody ops sums iter limbs = .ok (.done out)) :
    ∃ iterNext, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (none, iterNext) ∧ out = limbs := by
  change (do
    let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
    match o with
    | none => ok (ControlFlow.done limbs)
    | some limb => do
      let x ← Array.index_usize sums limb
      let low ← lift (x &&& 2147483647#u64)
      let high ← x >>> 31#i32
      let part ← low + high
      let old ← Array.index_usize limbs limb
      let new ← old + part
      let updated ← Array.update limbs limb new
      ok (ControlFlow.cont (iter1, updated))) = .ok (.done out) at hbody
  obtain ⟨outPair, hnext, hrest⟩ := bind_success _ _ _ hbody
  rcases outPair with ⟨option, iterNext⟩
  cases option with
  | none =>
    have hout : limbs = out := ControlFlow.done.inj (Result.ok.inj hrest)
    exact ⟨iterNext, hnext, hout.symm⟩
  | some limb =>
    obtain ⟨x, _, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨low, _, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨high, _, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨part, _, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨old, _, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨new, _, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨updated, _, hrest⟩ := bind_success _ _ _ hrest
    have hbad := Result.ok.inj hrest
    cases hbad

/-- Inverting one successful old body call yields its exact sequential fold
operation and concrete Range iterator advancement. Arithmetic Result
operations remain witnesses, not evaluated. -/
theorem body_continuation_fold
    (ops : Ops) (sums : Array U64 8#usize) (iter iter' : Range)
    (limbs limbs' : Array U64 8#usize)
    (hbody : LimbBody ops sums iter limbs = .ok (.cont (iter', limbs'))) :
    ∃ limb, limb = iter.start ∧
      iter.start.val < iter.end.val ∧
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some limb, iter') ∧
      iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end ∧
      foldSegment sums limbs limb = .ok limbs' := by
  change (do
    let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
    match o with
    | none => ok (ControlFlow.done limbs)
    | some limb => do
      let x ← Array.index_usize sums limb
      let low ← lift (x &&& 2147483647#u64)
      let high ← x >>> 31#i32
      let part ← low + high
      let old ← Array.index_usize limbs limb
      let new ← old + part
      let updated ← Array.update limbs limb new
      ok (ControlFlow.cont (iter1, updated))) = .ok (.cont (iter', limbs')) at hbody
  obtain ⟨out, hnext, hrest⟩ := bind_success _ _ _ hbody
  rcases out with ⟨option, iterNext⟩
  cases option with
  | none =>
    have hbad := Result.ok.inj hrest
    cases hbad
  | some limb =>
    simp only [bind_tc_ok] at hrest
    obtain ⟨x, hx, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨low, hlow, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨high, hhigh, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨part, hpart, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨old, hold, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨new, hnew, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨updated, hupdate, hrest⟩ := bind_success _ _ _ hrest
    have hfinish := Result.ok.inj hrest
    have hpair := ControlFlow.cont.inj hfinish
    rcases hpair with ⟨hiter, hlimbs⟩
    have hseg : foldSegment sums limbs limb = .ok limbs' := by
      unfold foldSegment
      simp only [hx, hlow, hhigh, hpart, hold, hnew, hupdate, bind_tc_ok]
    have hlt : iter.start.val < iter.end.val := by
      by_contra hnot
      have hn : iter.start.val ≥ iter.end.val := by omega
      have hnone := range_next_none_success iter hn
      rw [hnext] at hnone
      cases Result.ok.inj hnone
    rcases range_next_some_success iter hlt with ⟨expected, hnextExpected, hadvance, hend⟩
    have hnextEq := Result.ok.inj (hnext.symm.trans hnextExpected)
    rcases Prod.mk.inj hnextEq with ⟨hoption, hiter'⟩
    have hlimb : limb = iter.start := Option.some.inj hoption
    subst limb
    subst iter'
    exact ⟨iter.start, rfl, hlt, hnextExpected, hadvance, hend, hseg⟩

/-- Successful old loop execution emits an ordered chain of unchanged
single-limb fold operations. The proof is symbolic induction on remaining
range length; it does not unfold limb arithmetic. -/
theorem old_loop_success_fold_trace
    (ops : Ops) (sums : Array U64 8#usize) (iter : Range)
    (limbs out : Array U64 8#usize)
    (hbound : iter.start.val ≤ iter.end.val)
    (hloop : LimbLoop ops iter limbs sums = .ok out) :
    Nonempty (FoldTrace sums iter limbs out) := by
  let step : (Range × Array U64 8#usize) → Result
      (ControlFlow (Range × Array U64 8#usize) (Array U64 8#usize)) :=
    fun state => LimbBody ops sums state.1 state.2
  change Aeneas.Std.loop step (iter, limbs) = .ok out at hloop
  induction hmeasure : iter.end.val - iter.start.val using Nat.strong_induction_on
      generalizing iter limbs with
  | h n ih =>
    rcases loop_success_cases step (iter, limbs) out hloop with hdone | ⟨state', hcont, htail⟩
    · have hbody : LimbBody ops sums iter limbs = .ok (.done out) := by
        simpa only [step] using hdone
      obtain ⟨iterNext, hnext, hout⟩ := limb_body_done_range ops sums iter limbs out hbody
      have hnot : ¬ iter.start.val < iter.end.val := by
        by_contra hnot
        obtain ⟨_, hsome, _, _⟩ := range_next_some_success iter (by omega)
        rw [hnext] at hsome
        cases Result.ok.inj hsome
      exact ⟨FoldTrace.finish (by omega) hout⟩
    · rcases state' with ⟨iter', limbs'⟩
      have hbody : LimbBody ops sums iter limbs = .ok (.cont (iter', limbs')) := by
        simpa only [step] using hcont
      obtain ⟨limb, hlimb, hlt, hnext, hadvance, hend, hfold⟩ :=
        body_continuation_fold ops sums iter iter' limbs limbs' hbody
      rw [hlimb] at hfold
      have hn : iter.end.val - iter.start.val = n := hmeasure
      have hbound' : iter'.start.val ≤ iter'.end.val := by rw [hadvance, hend]; omega
      have hmeasure' : iter'.end.val - iter'.start.val < n := by
        rw [hadvance, hend]
        omega
      obtain ⟨tailTrace⟩ := ih _ hmeasure' iter' limbs' hbound' htail rfl
      exact ⟨FoldTrace.step (by omega) hadvance hend hfold tailTrace⟩

theorem old_loop_success_eight_ordered
    (ops : Ops) (sums limbs out : Array U64 8#usize)
    (hloop : LimbLoop ops { start := 0#usize, «end» := 8#usize } limbs sums = .ok out) :
    ∃ trace : FoldTrace sums { start := 0#usize, «end» := 8#usize } limbs out,
      trace.length = 8 := by
  let initial : Range := { start := 0#usize, «end» := 8#usize }
  obtain ⟨trace⟩ := old_loop_success_fold_trace ops sums initial limbs out (by simp [initial])
    (by simpa [LimbLoop, initial] using hloop)
  refine ⟨trace, ?_⟩
  rw [FoldTrace.length_eq_remaining trace]
  simp [initial]

#print axioms body_continuation_fold
#print axioms old_loop_success_fold_trace
#print axioms FoldTrace.length_eq_remaining
#print axioms old_loop_success_eight_ordered

end AspisR1FastDotsOldLimbLoopReverseV1
