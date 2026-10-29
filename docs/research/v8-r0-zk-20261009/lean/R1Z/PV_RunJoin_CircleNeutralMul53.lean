import R1Z.PV_RunJoin_CircleNeutralFoldOnce53
import R1Z.PV_RunJoin_CircleNeutralReduceCompare53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralMul53
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralCast53
open PV_RunJoin_CircleNeutralFold53 PV_RunJoin_CircleNeutralShift53

theorem complete (a b : U32) (ha : Canon a) (hb : Canon b) :
    ∃ y, PV_RunJoin_CircleRawScalar52.field.M31.mul a b = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.M31.mul a b = ok y ∧ Canon y := by
  let x := U64.wrapping_mul (UScalar.cast .U64 a) (UScalar.cast .U64 b)
  have hab : a.val*b.val < 4611686014132420609 := by
    have h := Nat.mul_lt_mul_of_lt_of_lt ha hb
    exact h
  have hx : x.val = a.val*b.val := by
    unfold x
    rw [PV_RunJoin_CircleNeutralWord53.mul64]
    · rw [up_val,up_val]
    · rw [up_val,up_val];omega
  obtain ⟨y,hy,hc⟩ := PV_RunJoin_CircleNeutralReduce53.total x
  have hsource : PV_RunJoin_CircleRawScalar52.field.M31.mul a b = ok y := by
    unfold PV_RunJoin_CircleRawScalar52.field.M31.mul PV_RunJoin_CircleRawScalar52.field.reduce_u64
    simp only [lift,bind_tc_ok]
    change (do let z ← PV_RunJoin_CircleRawScalar52.field.ct.reduce64 x; ok z) = ok y
    rw [hy,bind_tc_ok]
  refine ⟨y,hsource,?_,hc⟩
  have ha' : a < PV_RunJoin_CircleR72Raw52.field.P := ha
  have hb' : b < PV_RunJoin_CircleR72Raw52.field.P := hb
  unfold PV_RunJoin_CircleR72Raw52.field.M31.mul
  rw [if_pos ha',if_pos hb']
  simp only [lift,bind_tc_ok]
  rw [PV_RunJoin_CircleNeutralChecked64_53.mul _ _ (by rw [up_val,up_val];omega)]
  simp only [bind_tc_ok,low_mask,shr31i]
  rw [PV_RunJoin_CircleNeutralChecked64_53.add _ _ (fold_no_overflow x)]
  simp only [bind_tc_ok]
  have hfold : (fold x).val < 4294967294 :=
    PV_RunJoin_CircleNeutralFoldOnce53.product_fold_bound x (by rw [hx];exact hab)
  have hy' := (PV_RunJoin_CircleNeutralFoldOnce53.source x (by rw [hx];exact hab)).symm.trans hy
  change (if fold x ≥ UScalar.cast .U64 PV_RunJoin_CircleR72Raw52.field.P then do
    let z ← fold x - UScalar.cast .U64 PV_RunJoin_CircleR72Raw52.field.P
    ok (UScalar.cast .U32 z)
    else ok (UScalar.cast .U32 (fold x))) = ok y
  by_cases h : fold x ≥ UScalar.cast .U64 PV_RunJoin_CircleR72Raw52.field.P
  · rw [if_pos h,PV_RunJoin_CircleNeutralChecked64_53.sub _ _ h]
    simp only [lift,bind_tc_ok]
    have he : UScalar.cast .U32 (U64.wrapping_sub (fold x)
        (UScalar.cast .U64 PV_RunJoin_CircleR72Raw52.field.P)) =
        PV_RunJoin_CircleNeutralSubtract53.output (UScalar.cast .U32 (fold x)) := by
      apply UScalar.eq_of_val_eq
      have hv : 2147483647 ≤ (fold x).val := h
      have hs : (U64.wrapping_sub (fold x)
          (UScalar.cast .U64 PV_RunJoin_CircleR72Raw52.field.P)).val < 4294967296 := by
        rw [PV_RunJoin_CircleNeutralWord53.sub64 _ _ h]
        change (fold x).val-2147483647 < 4294967296
        omega
      rw [PV_RunJoin_CircleNeutralSubtract53.value,
        down_val (fold x) (by omega),if_pos hv,
        down_val _ hs,PV_RunJoin_CircleNeutralWord53.sub64 _ _ h]
      rfl
    rw [he]
    exact hy'
  · rw [if_neg h]
    have he : PV_RunJoin_CircleNeutralSubtract53.output (UScalar.cast .U32 (fold x)) =
        UScalar.cast .U32 (fold x) := by
      unfold PV_RunJoin_CircleNeutralSubtract53.output
      rw [if_neg (by change ¬ 2147483647 ≤ (UScalar.cast .U32 (fold x)).val;rw [down_val _ (by omega)];exact h)]
    simpa only [he] using hy'

#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralMul53
