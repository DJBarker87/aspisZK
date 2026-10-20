import Aeneas.Std.RangeIter
import S3VariantRowAeneasCut
import S3VariantRowLoopSteps
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1.S3VariantRowAeneasCut

def range0 : core.ops.range.Range Std.Usize := { start := 0#usize, «end» := 5#usize }
def range1 : core.ops.range.Range Std.Usize := { start := 1#usize, «end» := 5#usize }
def bodyOut0 (j out : Std.Usize) : Std.Usize :=
  out ||| (⟨(j &&& 3#usize).bv.shiftLeft 6⟩ : Std.Usize)

private theorem mul_eq_ok (x y z : Std.Usize)
    (hmax : x.val * y.val ≤ UScalar.max UScalarTy.Usize)
    (hout : z.val = x.val * y.val) :
    UScalar.mul x y = .ok z := by
  obtain ⟨v, hv, hvval⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := x) (y := y) hmax)
  have hEq : v = z := UScalar.eq_of_val_eq (by omega)
  rw [hEq] at hv
  exact hv

private theorem mul_two_zero : UScalar.mul (2#usize) (0#usize) = .ok (0#usize) := by
  apply mul_eq_ok
  · scalar_tac
  · scalar_tac

private theorem mul_two_three : UScalar.mul (2#usize) (3#usize) = .ok (6#usize) := by
  apply mul_eq_ok
  · scalar_tac
  · scalar_tac

private theorem shr_zero (j : Std.Usize) : UScalar.shiftRight_UScalar j (0#usize) = .ok j := by
  obtain ⟨z, hz, hv⟩ := WP.spec_imp_exists
    (UScalar.ShiftRight_spec j (0#usize) (by
      have hzero : (0#usize).val = 0 := by scalar_tac
      rw [hzero, UScalarTy.Usize_numBits_eq]
      rcases System.Platform.numBits_eq with h | h <;> omega))
  rcases hv with ⟨hval, _⟩
  have hEq : z = j := UScalar.eq_of_val_eq (by simpa using hval)
  rw [hEq] at hz
  exact hz

private theorem shl_six (x : Std.Usize) :
    UScalar.shiftLeft_UScalar x (6#usize) = .ok (⟨x.bv.shiftLeft 6⟩ : Std.Usize) := by
  obtain ⟨z, hz, hp⟩ := WP.spec_imp_exists
    (UScalar.ShiftLeft_spec x (6#usize) (UScalar.size UScalarTy.Usize)
      (by
        have hsix : (6#usize).val = 6 := by scalar_tac
        rw [hsix, UScalarTy.Usize_numBits_eq]
        rcases System.Platform.numBits_eq with h | h <;> omega) rfl)
  rcases hp with ⟨_, hbv⟩
  have hEq : z = ⟨x.bv.shiftLeft 6⟩ := by
    cases z
    cases x
    simp_all
  rw [hEq] at hz
  exact hz

private theorem next0 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize range0 =
      .ok (some 0#usize, range1) := by
  obtain ⟨out, hrun, hspec⟩ := WP.spec_imp_exists
    (Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst := core.clone.CloneUsize)
      (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) range0 (by simpa [range0] using (show (0#usize).val < (5#usize).val by scalar_tac)))
  rcases out with ⟨opt, iter1⟩
  rcases hspec with ⟨hopt, hstart, hend⟩
  cases hopt
  have hstartEq : iter1.start = 1#usize := by
    apply UScalar.eq_of_val_eq
    simpa [range0, range1] using hstart
  have hendEq : iter1.«end» = 5#usize := by
    simpa [range0, range1] using hend
  have hiter : iter1 = range1 := by
    cases iter1 with
    | mk st en =>
      change st = 1#usize at hstartEq
      change en = 5#usize at hendEq
      subst st
      subst en
      rfl
  have h0 : range0.start = 0#usize := rfl
  rw [hiter, h0] at hrun
  simpa only [core.iter.range.StepUsize] using hrun

def row_loop_continue (j d : Std.Usize)
    (iter : core.ops.range.Range Std.Usize) (out : Std.Usize) :
    Result (ControlFlow ((core.ops.range.Range Std.Usize) × Std.Usize) Std.Usize) := do
  let i ← 2#usize * d
  let i1 ← j >>> i
  let i2 ← lift (i1 &&& 3#usize)
  let i3 ← Array.index_usize tau d
  let i4 ← 2#usize * i3
  let i5 ← i2 <<< i4
  let out1 ← lift (out ||| i5)
  ok (cont (iter, out1))

theorem body0_continue (j out : Std.Usize) :
    row_loop_body j range0 out = row_loop_continue j 0#usize range1 out := by
  unfold row_loop_body row_loop_continue
  rw [next0]
  rfl

theorem continue_step_of_results
    (j d : Std.Usize) (iter : core.ops.range.Range Std.Usize) (out : Std.Usize)
    (i i1 t i4 i5 : Std.Usize)
    (hmul1 : UScalar.mul (2#usize) d = .ok i)
    (hshift : UScalar.shiftRight_UScalar j i = .ok i1)
    (hindex : Array.index_usize tau d = .ok t)
    (hmul2 : UScalar.mul (2#usize) t = .ok i4)
    (hleft : UScalar.shiftLeft_UScalar (i1 &&& 3#usize) i4 = .ok i5) :
    row_loop_continue j d iter out = .ok (.cont (iter, out ||| i5)) := by
  unfold row_loop_continue
  simp only [HMul.hMul, HShiftRight.hShiftRight, HShiftLeft.hShiftLeft]
  rw [hmul1]
  simp only [bind_tc_ok]
  rw [hshift]
  simp only [bind_tc_ok, lift]
  rw [hindex]
  simp only [bind_tc_ok]
  rw [hmul2]
  simp only [bind_tc_ok]
  rw [hleft]
  simp only [bind_tc_ok, lift]

private theorem tau_lookup_bounded (d : Std.Usize) (hd : d.val < 5) :
    ∃ t, Array.index_usize tau d = .ok t ∧ t.val ≤ 4 := by
  have hzero : (0#usize).val = 0 := by scalar_tac
  have hone : (1#usize).val = 1 := by scalar_tac
  have htwo : (2#usize).val = 2 := by scalar_tac
  have hthree : (3#usize).val = 3 := by scalar_tac
  have hfour : (4#usize).val = 4 := by scalar_tac
  by_cases h0 : d.val = 0
  · have hdEq : d = 0#usize := UScalar.eq_of_val_eq (by rw [h0, hzero])
    subst d
    exact ⟨3#usize, by simp [tau, Array.make, Array.index_usize], by scalar_tac⟩
  · by_cases h1 : d.val = 1
    · have hdEq : d = 1#usize := UScalar.eq_of_val_eq (by rw [h1, hone])
      subst d
      exact ⟨4#usize, by simp [tau, Array.make, Array.index_usize], by scalar_tac⟩
    · by_cases h2 : d.val = 2
      · have hdEq : d = 2#usize := UScalar.eq_of_val_eq (by rw [h2, htwo])
        subst d
        exact ⟨2#usize, by simp [tau, Array.make, Array.index_usize], by scalar_tac⟩
      · by_cases h3 : d.val = 3
        · have hdEq : d = 3#usize := UScalar.eq_of_val_eq (by rw [h3, hthree])
          subst d
          exact ⟨0#usize, by simp [tau, Array.make, Array.index_usize], by scalar_tac⟩
        · have h4 : d.val = 4 := by omega
          have hdEq : d = 4#usize := UScalar.eq_of_val_eq (by rw [h4, hfour])
          subst d
          exact ⟨1#usize, by simp [tau, Array.make, Array.index_usize], by scalar_tac⟩

theorem row_loop_continue_success (j d : Std.Usize)
    (iter : core.ops.range.Range Std.Usize) (out : Std.Usize)
    (hd : d.val < 5) :
    ∃ out', row_loop_continue j d iter out = .ok (.cont (iter, out')) := by
  obtain ⟨t, hindex, ht⟩ := tau_lookup_bounded d hd
  have hmul1max : (2#usize).val * d.val ≤ UScalar.max UScalarTy.Usize := by scalar_tac
  obtain ⟨i, hmul1, hi⟩ := WP.spec_imp_exists (UScalar.mul_spec hmul1max)
  have htwo : (2#usize).val = 2 := by scalar_tac
  have hiVal : i.val = 2 * d.val := by rw [htwo] at hi; exact hi
  have hbits8 : 8 < System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> omega
  have hiBits : i.val < UScalarTy.Usize.numBits := by
    rw [UScalarTy.Usize_numBits_eq, hiVal]
    have hd8 : 2 * d.val ≤ 8 := by omega
    omega
  obtain ⟨i1, hshift, _⟩ := WP.spec_imp_exists (UScalar.ShiftRight_spec j i hiBits)
  have hmul2max : (2#usize).val * t.val ≤ UScalar.max UScalarTy.Usize := by scalar_tac
  obtain ⟨i4, hmul2, hi4⟩ := WP.spec_imp_exists (UScalar.mul_spec hmul2max)
  have hi4Val : i4.val = 2 * t.val := by rw [htwo] at hi4; exact hi4
  have hi4Bits : i4.val < UScalarTy.Usize.numBits := by
    rw [UScalarTy.Usize_numBits_eq, hi4Val]
    have ht8 : 2 * t.val ≤ 8 := by omega
    omega
  obtain ⟨i5, hleft, _⟩ := WP.spec_imp_exists
    (UScalar.ShiftLeft_spec (i1 &&& 3#usize) i4 (UScalar.size UScalarTy.Usize)
      hi4Bits rfl)
  exact ⟨out ||| i5, continue_step_of_results j d iter out i i1 t i4 i5
    hmul1 hshift hindex hmul2 hleft⟩

theorem row_loop_body_from_next
    (j d : Std.Usize) (iter iter' : core.ops.range.Range Std.Usize)
    (out : Std.Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some d, iter')) :
    row_loop_body j iter out = row_loop_continue j d iter' out := by
  unfold row_loop_body row_loop_continue
  rw [hnext]
  rfl

theorem row_loop_body_step_success (j : Std.Usize)
    (iter : core.ops.range.Range Std.Usize) (out : Std.Usize)
    (hlt : iter.start.val < iter.end.val) (hend : iter.end.val ≤ 5) :
    ∃ iter' out', iter'.start.val = iter.start.val + 1 ∧
      iter'.end = iter.end ∧
      row_loop_body j iter out = .ok (.cont (iter', out')) := by
  obtain ⟨pair, hrun, hspec⟩ := WP.spec_imp_exists
    (Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst := core.clone.CloneUsize)
      (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) iter hlt)
  rcases pair with ⟨opt, iter'⟩
  rcases hspec with ⟨hopt, hstart, hfinish⟩
  rw [hopt] at hrun
  obtain ⟨out', hout⟩ := row_loop_continue_success j iter.start iter' out (by omega)
  refine ⟨iter', out', hstart, hfinish, ?_⟩
  rw [row_loop_body_from_next j iter.start iter iter' out hrun]
  exact hout

theorem continue0_eq (j out : Std.Usize) :
    row_loop_continue j 0#usize range1 out = .ok (.cont (range1, bodyOut0 j out)) := by
  unfold row_loop_continue
  simp only [HMul.hMul]
  rw [mul_two_zero]
  simp only [bind_tc_ok]
  simp only [HShiftRight.hShiftRight]
  rw [shr_zero]
  simp only [bind_tc_ok, lift]
  rw [show Array.index_usize tau 0#usize = .ok 3#usize by
    simp [tau, Array.make, Array.index_usize]]
  simp only [bind_tc_ok]
  rw [mul_two_three]
  simp only [bind_tc_ok]
  simp only [HShiftLeft.hShiftLeft]
  rw [shl_six]
  simp only [bind_tc_ok, lift, bodyOut0]

theorem body0_eq (j out : Std.Usize) :
    row_loop_body j range0 out = .ok (.cont (range1, bodyOut0 j out)) := by
  rw [body0_continue, continue0_eq]

end AspisR1.S3VariantRowAeneasCut
#print axioms AspisR1.S3VariantRowAeneasCut.body0_continue
#print axioms AspisR1.S3VariantRowAeneasCut.continue0_eq
#print axioms AspisR1.S3VariantRowAeneasCut.row_loop_continue_success
#print axioms AspisR1.S3VariantRowAeneasCut.row_loop_body_step_success
#print axioms AspisR1.S3VariantRowAeneasCut.body0_eq
#print axioms AspisR1.S3VariantRowAeneasCut.continue_step_of_results
