import R1Z.PV_RunJoin_R24Inputs54
import R1Z.PV_RunJoin_NeutralTowerValue54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_R24PartialValues54
open PV_RunJoin_NeutralValue54 PV_RunJoin_NeutralTowerValue54 PV_RunJoin_CircleNeutralShape53
open PV_RunJoin_R24Inputs54

theorem square_zero : ((4611686014132420609 : Nat) : M)=0 := by
  rw [show (4611686014132420609:Nat)=2147483647*2147483647 from rfl,Nat.cast_mul,prime_zero,mul_zero]

theorem u_value (a b : Q) (ha : QC a) (hb : QC b) :
    (u a b : M)=scalar a.2.1*scalar b.2.1-scalar a.2.2*scalar b.2.2 := by
  have hcg := PV_RunJoin_CircleNeutralR24Bounds53.product _ _ ha.2.1 hb.2.1
  have hdh := PV_RunJoin_CircleNeutralR24Bounds53.product _ _ ha.2.2 hb.2.2
  have hle : a.2.2.val*b.2.2.val≤a.2.1.val*b.2.1.val+4611686014132420609 := by omega
  unfold u
  rw [fold,Nat.cast_sub hle,Nat.cast_add,Nat.cast_mul,Nat.cast_mul,square_zero,add_zero]
  rfl

theorem v_value (a b : Q) :
    (v a b : M)=scalar a.2.1*scalar b.2.2+scalar a.2.2*scalar b.2.1 := by
  unfold v
  rw [fold,Nat.cast_add,Nat.cast_mul,Nat.cast_mul]
  rfl
#print axioms square_zero
#print axioms u_value
#print axioms v_value
end R1Z.PV_RunJoin_R24PartialValues54
