import R1Z.PV_RunJoin_R24Cell3_54
import R1Z.PV_RunJoin_CircleNeutralR24Word53
import R1Z.PV_RunJoin_CircleNeutralR24Bounds53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_R24Equation3_54
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralR24Word53
abbrev Q := (U32 × U32) × (U32 × U32)
def accumulator (left right : Q) (u v : Nat) : Nat := left.1.1.val*right.2.2.val+left.1.2.val*right.2.1.val+left.2.1.val*right.1.2.val+left.2.2.val*right.1.1.val
theorem complete (left right : Q) (hl : QC left) (hr : QC right)
    (u v : Nat) (hu : u<6442450941) (hv : v<6442450941) :
    PV_RunJoin_R24Cell3_54.cell left right (word u) (word v)=
      PV_RunJoin_CircleR72Raw52.field.M31.reduce_u64 (word (accumulator left right u v)) := by
  have h0 : left.1.1.val<2147483647 := hl.1.1
  have h1 : left.1.2.val<2147483647 := hl.1.2
  have h2 : left.2.1.val<2147483647 := hl.2.1
  have h3 : left.2.2.val<2147483647 := hl.2.2
  have h4 : right.1.1.val<2147483647 := hr.1.1
  have h5 : right.1.2.val<2147483647 := hr.1.2
  have h6 : right.2.1.val<2147483647 := hr.2.1
  have h7 : right.2.2.val<2147483647 := hr.2.2
  have hae : left.1.1.val*right.1.1.val<4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt h0 h4
  have haf : left.1.1.val*right.1.2.val<4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt h0 h5
  have hag : left.1.1.val*right.2.1.val<4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt h0 h6
  have hah : left.1.1.val*right.2.2.val<4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt h0 h7
  have hbe : left.1.2.val*right.1.1.val<4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt h1 h4
  have hbf : left.1.2.val*right.1.2.val<4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt h1 h5
  have hbg : left.1.2.val*right.2.1.val<4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt h1 h6
  have hbh : left.1.2.val*right.2.2.val<4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt h1 h7
  have hce : left.2.1.val*right.1.1.val<4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt h2 h4
  have hcf : left.2.1.val*right.1.2.val<4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt h2 h5
  have hcg : left.2.1.val*right.2.1.val<4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt h2 h6
  have hch : left.2.1.val*right.2.2.val<4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt h2 h7
  have hde : left.2.2.val*right.1.1.val<4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt h3 h4
  have hdf : left.2.2.val*right.1.2.val<4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt h3 h5
  have hdg : left.2.2.val*right.2.1.val<4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt h3 h6
  have hdh : left.2.2.val*right.2.2.val<4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt h3 h7
  have hsquare : PV_RunJoin_CircleNeutralR24Leaf53.square=word 4611686014132420609 := by
    apply UScalar.eq_of_val_eq
    rw [PV_RunJoin_CircleNeutralR24Leaf53.square_val,value _ (by decide)]
  have hprime : core.convert.num.FromU64U32.from PV_RunJoin_CircleR72Raw52.field.P=word 2147483647 := rfl
  unfold PV_RunJoin_R24Cell3_54.cell accumulator
  simp only [widen,hsquare,hprime,show (2#u64)=word 2 from rfl,show (3#u64)=word 3 from rfl,lift,bind_tc_ok]
  rw [mul _ _ (by omega) (by omega) (by omega),bind_tc_ok]
  rw [mul _ _ (by omega) (by omega) (by omega),bind_tc_ok]
  rw [add]
  rw [mul _ _ (by omega) (by omega) (by omega),bind_tc_ok]
  rw [add]
  rw [mul _ _ (by omega) (by omega) (by omega),bind_tc_ok]
  rw [add]
  cases PV_RunJoin_CircleR72Raw52.field.M31.reduce_u64 _ <;> rfl
#print axioms accumulator
#print axioms complete
end R1Z.PV_RunJoin_R24Equation3_54
