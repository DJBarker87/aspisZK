import Aeneas.Std.RangeIter
import S3VariantRowAeneasCut
import S3VariantRowLoopSteps
import S3VariantRowBodyProbe

open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1.S3VariantRowAeneasCut

theorem s2_row_result_total (j : Std.Usize) :
    ∃ out, s2_row_result j = .ok out := by
  have hwp : WP.spec (row_loop range0 j 0#usize) (fun _ : Std.Usize => True) := by
    unfold row_loop
    refine loop.spec_decr_nat
      (fun s : core.ops.range.Range Std.Usize × Std.Usize => 5 - s.1.start.val)
      (fun s : core.ops.range.Range Std.Usize × Std.Usize =>
        s.1.start.val ≤ 5 ∧ s.1.end.val = 5)
      (fun _ : Std.Usize => True)
      (fun s : core.ops.range.Range Std.Usize × Std.Usize => row_loop_body j s.1 s.2)
      (range0, 0#usize) ?_ ?_
    · intro s hs
      rcases s with ⟨iter, out⟩
      rcases hs with ⟨hstart, hend⟩
      by_cases hlt : iter.start.val < iter.end.val
      · obtain ⟨iterNext, outNext, hstartNext, hendNext, hbody⟩ :=
          row_loop_body_step_success j iter out hlt (by rw [hend])
        rw [hbody, WP.spec_ok]
        change (iterNext.start.val ≤ 5 ∧ iterNext.end.val = 5) ∧
          5 - iterNext.start.val < 5 - iter.start.val
        constructor
        · constructor
          · have hstep : iterNext.start.val = iter.start.val + 1 := hstartNext
            rw [hstep]
            have hlt5 : iter.start.val < 5 := by rw [hend] at hlt; exact hlt
            omega
          · rw [hendNext, hend]
        · have hstep : iterNext.start.val = iter.start.val + 1 := hstartNext
          rw [hstep]
          have hlt5 : iter.start.val < 5 := by rw [hend] at hlt; exact hlt
          omega
      · have hge : iter.start.val ≥ iter.end.val := Nat.le_of_not_gt hlt
        have hdone := row_loop_body_done j iter out hge
        rw [hdone, WP.spec_ok]
        trivial
    · constructor
      · change (0 : Nat) ≤ 5
        omega
      · change (5 : Nat) = 5
        rfl
  obtain ⟨out, hout, _⟩ := WP.spec_imp_exists hwp
  refine ⟨out, ?_⟩
  simpa [s2_row_result, range0] using hout

end AspisR1.S3VariantRowAeneasCut

#print axioms AspisR1.S3VariantRowAeneasCut.s2_row_result_total
