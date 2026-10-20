import Aeneas.Std.RangeIter
import S3VariantRowAeneasCut
import S3VariantRowLoopSteps
import S3VariantRowBodyValue
import Mathlib.Data.Nat.Bitwise

open Aeneas Aeneas.Std Result ControlFlow WP
namespace AspisR1.S3VariantRowAeneasCut

def tauSlot : Nat → Nat
  | 0 => 3
  | 1 => 4
  | 2 => 2
  | 3 => 0
  | _ => 1

def rowTerm (j d : Nat) : Nat :=
  ((j >>> (2 * d)) &&& 3) * 2 ^ (2 * tauSlot d)

def rowPrefix (j : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => rowPrefix j k ||| rowTerm j k

private theorem tau_index_exact (d : Std.Usize) (hd : d.val < 5) :
    ∃ t, Array.index_usize tau d = .ok t ∧ t.val = tauSlot d.val := by
  have hzero : (0#usize).val = 0 := by scalar_tac
  have hone : (1#usize).val = 1 := by scalar_tac
  have htwo : (2#usize).val = 2 := by scalar_tac
  have hthree : (3#usize).val = 3 := by scalar_tac
  have hfour : (4#usize).val = 4 := by scalar_tac
  by_cases h0 : d.val = 0
  · have hdEq : d = 0#usize := UScalar.eq_of_val_eq (by rw [h0, hzero])
    subst d
    exact ⟨3#usize, by simp [tau, Array.make, Array.index_usize], by simp [tauSlot]⟩
  · by_cases h1 : d.val = 1
    · have hdEq : d = 1#usize := UScalar.eq_of_val_eq (by rw [h1, hone])
      subst d
      exact ⟨4#usize, by simp [tau, Array.make, Array.index_usize], by simp [tauSlot]⟩
    · by_cases h2 : d.val = 2
      · have hdEq : d = 2#usize := UScalar.eq_of_val_eq (by rw [h2, htwo])
        subst d
        exact ⟨2#usize, by simp [tau, Array.make, Array.index_usize], by simp [tauSlot]⟩
      · by_cases h3 : d.val = 3
        · have hdEq : d = 3#usize := UScalar.eq_of_val_eq (by rw [h3, hthree])
          subst d
          exact ⟨0#usize, by simp [tau, Array.make, Array.index_usize], by simp [tauSlot]⟩
        · have h4 : d.val = 4 := by omega
          have hdEq : d = 4#usize := UScalar.eq_of_val_eq (by rw [h4, hfour])
          subst d
          exact ⟨1#usize, by simp [tau, Array.make, Array.index_usize], by simp [tauSlot]⟩

theorem row_loop_body_prefix_step (j : Std.Usize)
    (iter : core.ops.range.Range Std.Usize) (out : Std.Usize)
    (hlt : iter.start.val < iter.end.val) (hend : iter.end.val = 5) :
    ∃ iter' out',
      iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end ∧
      row_loop_body j iter out = .ok (.cont (iter', out')) ∧
      out'.val = out.val ||| rowTerm j.val iter.start.val := by
  have hbound : iter.end.val ≤ 5 := by rw [hend]
  obtain ⟨pair, hrun, hspec⟩ := WP.spec_imp_exists
    (Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst := core.clone.CloneUsize)
      (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) iter hlt)
  rcases pair with ⟨opt, iter'⟩
  rcases hspec with ⟨hopt, hstart, hfinish⟩
  rw [hopt] at hrun
  obtain ⟨t, ht, htval⟩ := tau_index_exact iter.start (by rw [hend] at hlt; exact hlt)
  obtain ⟨t', out', hindex, hcontinue, houtval⟩ :=
    row_loop_continue_value j iter.start iter' out (by rw [hend] at hlt; exact hlt)
  have hteq : t' = t := Result.ok.inj (hindex.symm.trans ht)
  subst t'
  have hbody : row_loop_body j iter out = .ok (.cont (iter', out')) := by
    rw [row_loop_body_from_next j iter.start iter iter' out hrun]
    exact hcontinue
  refine ⟨iter', out', hstart, hfinish, hbody, ?_⟩
  rw [houtval, htval]
  rfl

theorem s2_row_result_prefix (j : Std.Usize) :
    ∃ out, s2_row_result j = .ok out ∧ out.val = rowPrefix j.val 5 := by
  have hwp : WP.spec (row_loop range0 j 0#usize)
      (fun out : Std.Usize => out.val = rowPrefix j.val 5) := by
    unfold row_loop
    refine loop.spec_decr_nat
      (fun s : core.ops.range.Range Std.Usize × Std.Usize => 5 - s.1.start.val)
      (fun s : core.ops.range.Range Std.Usize × Std.Usize =>
        s.1.start.val ≤ 5 ∧ s.1.end.val = 5 ∧ s.2.val = rowPrefix j.val s.1.start.val)
      (fun out : Std.Usize => out.val = rowPrefix j.val 5)
      (fun s : core.ops.range.Range Std.Usize × Std.Usize => row_loop_body j s.1 s.2)
      (range0, 0#usize) ?_ ?_
    · intro s hs
      rcases s with ⟨iter, out⟩
      rcases hs with ⟨hstart, hend, hvalue⟩
      by_cases hlt : iter.start.val < iter.end.val
      · obtain ⟨iterNext, outNext, hstartNext, hendNext, hbody, hout⟩ :=
          row_loop_body_prefix_step j iter out hlt hend
        rw [hbody, WP.spec_ok]
        change (iterNext.start.val ≤ 5 ∧ iterNext.end.val = 5 ∧
            outNext.val = rowPrefix j.val iterNext.start.val) ∧
          5 - iterNext.start.val < 5 - iter.start.val
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · have hlt5 : iter.start.val < 5 := by rw [hend] at hlt; exact hlt
          have hstep : iterNext.start.val = iter.start.val + 1 := hstartNext
          omega
        · rw [hendNext, hend]
        · rw [hout, hvalue, hstartNext]
          simp only [rowPrefix]
        · have hlt5 : iter.start.val < 5 := by rw [hend] at hlt; exact hlt
          have hstep : iterNext.start.val = iter.start.val + 1 := hstartNext
          omega
      · have hge : iter.start.val ≥ iter.end.val := Nat.le_of_not_gt hlt
        have hdone := row_loop_body_done j iter out hge
        rw [hdone, WP.spec_ok]
        change out.val = rowPrefix j.val 5
        have hstartLe : iter.start.val ≤ 5 := by exact hstart
        have hstartEq : iter.start.val = 5 := by
          have hge' : iter.start.val ≥ 5 := by rw [hend] at hge; exact hge
          omega
        rw [hstartEq] at hvalue
        exact hvalue
    · constructor
      · change (0 : Nat) ≤ 5
        omega
      · constructor
        · change (5 : Nat) = 5
          rfl
        · change (0#usize).val = rowPrefix j.val 0
          simp [rowPrefix]
  obtain ⟨out, hout, houtValue⟩ := WP.spec_imp_exists hwp
  refine ⟨out, ?_, houtValue⟩
  simpa [s2_row_result, range0] using hout

end AspisR1.S3VariantRowAeneasCut
#print axioms AspisR1.S3VariantRowAeneasCut.row_loop_body_prefix_step
#print axioms AspisR1.S3VariantRowAeneasCut.s2_row_result_prefix
