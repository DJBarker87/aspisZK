import R1Z.PV_RunJoin_R24Equation1_54
import R1Z.PV_RunJoin_R24Reduce54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_R24Residue1_54
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralR24Word53
abbrev Q := (U32 × U32) × (U32 × U32)
theorem complete (left right : Q) (hl : QC left) (hr : QC right)
    (u v : Nat) (hu : u<6442450941) (hv : v<6442450941) :
    ∃ y, PV_RunJoin_R24Cell1_54.cell left right (word u) (word v)=ok y ∧
      Canon y ∧ y.val=PV_RunJoin_R24Equation1_54.accumulator left right u v % 2147483647 := by
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
  have hn : PV_RunJoin_R24Equation1_54.accumulator left right u v<18446744073709551616 := by
    unfold PV_RunJoin_R24Equation1_54.accumulator
    omega
  obtain ⟨y,hy,hc,hres⟩ := PV_RunJoin_R24Reduce54.complete _ hn
  exact ⟨y,(PV_RunJoin_R24Equation1_54.complete left right hl hr u v hu hv).trans hy,hc,hres⟩
#print axioms complete
end R1Z.PV_RunJoin_R24Residue1_54
