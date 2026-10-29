import R1Z.PV_RunJoin_CircleNeutralMul53
import R1Z.PV_RunJoin_CircleNeutralResidue53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralMulResidue53
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralCast53

theorem complete (a b : U32) (ha : Canon a) (hb : Canon b) :
    ∃ y, PV_RunJoin_CircleRawScalar52.field.M31.mul a b = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.M31.mul a b = ok y ∧
      y.val = (a.val*b.val)%2147483647 := by
  let x := U64.wrapping_mul (UScalar.cast .U64 a) (UScalar.cast .U64 b)
  have hab : a.val*b.val < 4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt ha hb
  have hx : x.val = a.val*b.val := by
    unfold x
    rw [PV_RunJoin_CircleNeutralWord53.mul64]
    · rw [up_val,up_val]
    · rw [up_val,up_val];omega
  obtain ⟨y,hy,hy',hc⟩ := PV_RunJoin_CircleNeutralMul53.complete a b ha hb
  obtain ⟨z,hz,hres⟩ := PV_RunJoin_CircleNeutralResidue53.reduce_mod x
  have hsource : PV_RunJoin_CircleRawScalar52.field.M31.mul a b = ok z := by
    unfold PV_RunJoin_CircleRawScalar52.field.M31.mul PV_RunJoin_CircleRawScalar52.field.reduce_u64
    simp only [lift,bind_tc_ok]
    change (do let q ← PV_RunJoin_CircleRawScalar52.field.ct.reduce64 x;ok q) = ok z
    rw [hz,bind_tc_ok]
  have he : y=z := Result.ok.inj (hy.symm.trans hsource)
  exact ⟨y,hy,hy',by rw [he,hres,hx]⟩

#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralMulResidue53
