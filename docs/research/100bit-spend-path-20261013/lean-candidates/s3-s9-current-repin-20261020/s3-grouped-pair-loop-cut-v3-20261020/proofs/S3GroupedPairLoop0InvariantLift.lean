import AspisR1GroupedPairCut.Funs
import Aeneas.Std.RangeIter

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
namespace AspisR1GroupedPairCut.Proofs

abbrev GroupedCoeffArray := Array field.WideExact 12#usize

/-- Lift a local success/meaning contract for the emitted first accumulation
loop to a whole-loop result.  The caller supplies the semantic prefix meaning;
this theorem handles the actual `loop` driver, its finite range, and terminal
branch. -/
theorem grouped_pair_loop0_lift_prefix
    (ops : weights.WideExactOps)
    (coeff : Array field.WideExact 64#usize)
    (iter0 : core.ops.range.Range Std.Usize)
    (initial : GroupedCoeffArray)
    (Meaning : Nat → GroupedCoeffArray → Prop)
    (hstart : iter0.start.val = 0)
    (hend : iter0.end.val = 64)
    (hinitial : Meaning 0 initial)
    (hstep : ∀ (iter : core.ops.range.Range Std.Usize)
      (a : GroupedCoeffArray),
      iter.end.val = 64 → iter.start.val < iter.end.val →
      Meaning iter.start.val a →
      ∃ (iterNext : core.ops.range.Range Std.Usize) (aNext : GroupedCoeffArray),
        iterNext.start.val = iter.start.val + 1 ∧
        iterNext.end = iter.end ∧
        weights.s2_grouped_inactive_pair_loop0.body ops coeff iter a =
          .ok (.cont (iterNext, aNext)) ∧
        Meaning iterNext.start.val aNext)
    (hdone : ∀ (iter : core.ops.range.Range Std.Usize)
      (a : GroupedCoeffArray),
      iter.end.val = 64 → iter.start.val ≥ iter.end.val →
      Meaning iter.start.val a →
      weights.s2_grouped_inactive_pair_loop0.body ops coeff iter a = .ok (.done a) ∧
      Meaning 64 a) :
    ∃ result : GroupedCoeffArray,
      weights.s2_grouped_inactive_pair_loop0 ops iter0 coeff initial = .ok result ∧
      Meaning 64 result := by
  have hwp : WP.spec (weights.s2_grouped_inactive_pair_loop0 ops iter0 coeff initial)
      (fun result : GroupedCoeffArray => Meaning 64 result) := by
    unfold weights.s2_grouped_inactive_pair_loop0
    refine loop.spec_decr_nat
      (fun s : core.ops.range.Range Std.Usize × GroupedCoeffArray => 64 - s.1.start.val)
      (fun s : core.ops.range.Range Std.Usize × GroupedCoeffArray =>
        s.1.start.val ≤ 64 ∧ s.1.end.val = 64 ∧ Meaning s.1.start.val s.2)
      (fun result : GroupedCoeffArray => Meaning 64 result)
      (fun s : core.ops.range.Range Std.Usize × GroupedCoeffArray =>
        weights.s2_grouped_inactive_pair_loop0.body ops coeff s.1 s.2)
      (iter0, initial) ?_ ?_
    · intro s hs
      rcases s with ⟨iter, a⟩
      rcases hs with ⟨hstartBound, hendState, hmeaning⟩
      by_cases hlt : iter.start.val < iter.end.val
      · obtain ⟨iterNext, aNext, hnextStart, hnextEnd, hbody, hnextMeaning⟩ :=
          hstep iter a hendState hlt hmeaning
        have hlt64 : iter.start.val < 64 := by
          rw [hendState] at hlt
          exact hlt
        have hnextEndVal : iterNext.end.val = iter.end.val :=
          congrArg UScalar.val hnextEnd
        rw [hbody, WP.spec_ok]
        change (iterNext.start.val ≤ 64 ∧ iterNext.end.val = 64 ∧
            Meaning iterNext.start.val aNext) ∧
          64 - iterNext.start.val < 64 - iter.start.val
        refine ⟨⟨?_, ?_, hnextMeaning⟩, ?_⟩
        · rw [hnextStart]
          omega
        · rw [hnextEndVal, hendState]
        · rw [hnextStart]
          omega
      · have hge : iter.start.val ≥ iter.end.val := Nat.le_of_not_gt hlt
        obtain ⟨hdoneBody, hfinal⟩ := hdone iter a hendState hge hmeaning
        rw [hdoneBody, WP.spec_ok]
        exact hfinal
    · refine ⟨?_, ?_, ?_⟩
      · rw [hstart]
        omega
      · exact hend
      · rw [hstart]
        exact hinitial
  obtain ⟨result, hresult, hmeaning⟩ := WP.spec_imp_exists hwp
  exact ⟨result, hresult, hmeaning⟩

end AspisR1GroupedPairCut.Proofs
#print axioms AspisR1GroupedPairCut.Proofs.grouped_pair_loop0_lift_prefix
