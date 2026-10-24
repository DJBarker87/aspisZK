import S9PartialDotReaderDomainV1
import S9ActualDotRangeBoundsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9PartialDotActualReaderCallsV1
open AspisR1S9PartialDotReaderDomainV1
open AspisR1S9NativeFieldS5BoundedReaderV1
abbrev Iter := core.ops.range.Range Usize
abbrev Dot := fast_pairing.EbyKDot
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Common := Array aspis_core.field.QM31 16#usize
private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m; next x)=.ok out) : ∃ x,m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- Exact source partial-dot step. Both wrapping offset operations are
accounted for before deriving the bounded same-index S5 reader call. -/
theorem body_success_reader_call (f : Slice U8) (common : Common) (s : Usize)
    (iter : Iter) (dot : Dot)
    (flow : ControlFlow (Iter × Dot) (core.result.Result W verifier.Error))
    (hs : s.val < 4) (hend : iter.end.val ≤ 16)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok (64#usize))
    (hb : weights.partial_dot_loop.body f common s iter dot=.ok flow) :
    (∃ it, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (none,it)) ∨
    ∃ (j : Usize) (it : Iter) (w : W) (q : aspis_core.field.QM31)
      (r : core.result.Result Unit Unit) (dotNext : Dot),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some j,it) ∧
      j.val < 16 ∧ (index s j).val=16*s.val+j.val ∧ (index s j).val < 64 ∧
      weights.field f (index s j)=.ok w ∧ Array.index_usize common j=.ok q ∧
      fast_pairing.EbyKDot.push dot w q=.ok (r,dotNext) ∧
      AspisR1S5PairCutTransparentReaderV1.readerBody
        AspisR1S5PairCutTransparentReaderV1.actualPairDecoder f (index s j)=.ok (toS5 w) := by
  unfold weights.partial_dot_loop.body at hb
  obtain ⟨next,hn,hb⟩ := bind_success _ _ _ hb
  rcases next with ⟨opt,it⟩
  cases opt with
  | none => exact Or.inl ⟨it,hn⟩
  | some j =>
    simp only [lift,bind_tc_ok] at hb
    obtain ⟨w,hw,hb⟩ := bind_success _ _ _ hb
    obtain ⟨q,hq,hb⟩ := bind_success _ _ _ hb
    obtain ⟨p,hp,hb⟩ := bind_success _ _ _ hb
    rcases p with ⟨r,dotNext⟩
    obtain ⟨hj,hlt,hstart,he⟩ :=
      AspisR1S9ActualDotRangeBoundsV1.range_next_index_bounds iter it j hn
    have hj16 : j.val < 16 := by omega
    have hindex := index_exact s j hs hj16
    have hw' : weights.field f (index s j)=.ok w := hw
    have hm := index_maps_s5_reader f s j hs hj16 hdiv
    have hr : AspisR1S5PairCutTransparentReaderV1.readerBody
        AspisR1S5PairCutTransparentReaderV1.actualPairDecoder f (index s j)=.ok (toS5 w) := by
      rw [hw'] at hm
      exact hm.symm
    exact Or.inr ⟨j,it,w,q,r,dotNext,hn,hj16,hindex.1,hindex.2,hw',hq,hp,hr⟩

/-- The actual outer shared-partials source loop supplies s<4 to every
partial-dot invocation as soon as its iterator end is known to be4. The
callee success is derived from the SAME successful source body. -/
theorem shared_body_success_partial_call
    (f : Slice U8) (common : Common) (iter : Iter) (partials : Array W 4#usize)
    (flow : ControlFlow (Iter × Array W 4#usize) (core.result.Result (Array W 4#usize) verifier.Error))
    (hend : iter.end.val ≤ 4)
    (hb : weights.shared_partials_loop.body f common iter partials=.ok flow) :
    (∃ it, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (none,it)) ∨
    ∃ (s : Usize) (it : Iter) (r : core.result.Result W verifier.Error),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some s,it) ∧
      s.val < 4 ∧ weights.partial_dot f common s=.ok r := by
  unfold weights.shared_partials_loop.body at hb
  obtain ⟨next,hn,hb⟩ := bind_success _ _ _ hb
  rcases next with ⟨opt,it⟩
  cases opt with
  | none => exact Or.inl ⟨it,hn⟩
  | some s =>
    obtain ⟨r,hr,hb⟩ := bind_success _ _ _ hb
    have hlt := (AspisR1S9ActualDotRangeBoundsV1.range_next_index_bounds iter it s hn).2.1
    exact Or.inr ⟨s,it,r,hn,by omega,hr⟩

#print axioms body_success_reader_call
#print axioms shared_body_success_partial_call
end AspisR1S9PartialDotActualReaderCallsV1
