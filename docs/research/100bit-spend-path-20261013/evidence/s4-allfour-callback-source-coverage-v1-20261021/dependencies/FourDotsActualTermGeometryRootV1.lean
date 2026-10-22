import FourDotsActualTermTraceRootV1
import Mathlib.Data.List.Range
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsActualTermGeometryRootV1
open AspisR1FastDotsActualTermTraceRootV1
abbrev U8 := Std.U8
abbrev U64 := Std.U64
private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem term_body_done_exhausted (ops : Ops)
    (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (iter : Range) (sums out : Array U64 8#usize)
    (hbody : TermBody ops a a1 slot iter sums = .ok (.done out)) : iter.end.val ≤ iter.start.val := by
  unfold TermBody at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none =>
      have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
        (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
        (by intros; rfl) (by intros; rfl) iter
      rw [hnext,WP.spec_ok] at hspec
      by_cases hlt : iter.start.val < iter.end.val
      · simp only [hlt,↓reduceIte] at hspec
        rcases hspec with ⟨⟨hopt,_⟩,_⟩
        cases hopt
      · omega
  | some _ =>
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      cases Result.ok.inj hrest

private theorem next_some_progress (iter iter' : Range) (term : Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some term,iter')) :
    term = iter.start ∧ iter.start.val < iter.end.val ∧
      iter'.start.val = iter.start.val+1 ∧ iter'.end = iter.end := by
  have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
    (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
    (by intros; rfl) (by intros; rfl) iter
  rw [hnext,WP.spec_ok] at hspec
  by_cases hlt : iter.start.val < iter.end.val
  · simp only [hlt,↓reduceIte] at hspec
    rcases hspec with ⟨⟨hterm,hadvance⟩,hend⟩
    exact ⟨Option.some.inj hterm,hlt,hadvance,hend⟩
  · simp only [hlt,↓reduceIte] at hspec
    rcases hspec with ⟨⟨hnone,_⟩,_⟩
    cases hnone

/-- Retained actual source contributions visit precisely the selected range
in order, with no omitted or repeated term index. -/
theorem actual_trace_term_indices
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (iter : Range) (sums out : Array U64 8#usize) (cs : List Contribution)
    (htrace : ActualTermTrace ops a a1 slot iter sums out cs) :
    cs.map (fun c => c.term.val) = List.range' iter.start.val (iter.end.val-iter.start.val) := by
  induction htrace with
  | done iter sums hbody =>
      have hexhaust := term_body_done_exhausted ops a a1 slot iter sums sums hbody
      have hdiff : iter.end.val-iter.start.val = 0 := by omega
      simp only [List.map_nil,hdiff,List.range'_zero]
  | @step iter iter' sums sums' out c tail hbody hmatch hvalue htail ih =>
      obtain ⟨hterm,hlt,hadvance,hend⟩ := next_some_progress iter iter' c.term hmatch.1
      have hdiff : iter.end.val-iter.start.val =
          (iter'.end.val-iter'.start.val)+1 := by rw [hend,hadvance]; omega
      simp only [List.map_cons,ih,hterm,hdiff,List.range'_succ]
      rw [hadvance]

#print axioms actual_trace_term_indices
end AspisR1FastDotsActualTermGeometryRootV1
