import R1Z.PV_RunJoin_WeightFactorWrite47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightFactorWriteCps47
open Aeneas Aeneas.Std Result
open PV_B2_C_ConstructorRows (Factors)
open PV_B2_F_ConstructorCarrier (K)
open PV_RunJoin_WeightFactorWrite47 (write)

theorem complete {A : Type} (fs : Factors) (slot d : Usize)
    (row : Array K 4#usize) (k : Factors → Result A) :
    (write fs slot d row >>=k)=(do
      let (m,back) ← Array.index_mut_usize fs slot
      let m1 ← Array.update m d row
      k (back m1)) := by
  unfold write
  cases h : Array.index_mut_usize fs slot with
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]
  | ok pair =>
    rcases pair with ⟨m,back⟩
    simp only [h,bind_tc_ok]
    change ((do let m1 ← Array.update m d row;ok (back m1)) >>=k)=
      (do let m1 ← Array.update m d row;k (back m1))
    simp only [bind_assoc,bind_tc_ok]
#print axioms complete
end R1Z.PV_RunJoin_WeightFactorWriteCps47
