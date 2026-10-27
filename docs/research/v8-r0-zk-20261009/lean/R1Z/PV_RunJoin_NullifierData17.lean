import R1Z.PV_RunJoin_HashCallback17
import R1Z.PV_RunJoin_LeafLift16
import R1Z.PV_RunJoin_FixtureNullifier
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NullifierData17
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
def s4_0 : State := Array.make 16#usize [11#u32,28#u32,45#u32,62#u32,79#u32,96#u32,113#u32,130#u32,1095958530#u32,16#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
theorem lift4_0 : liftA (K := PV_RunJoin_FixtureRecords.M) s4_0 = PV_RunJoin_FixtureHashModel.s_4_0 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift4_0
theorem canon4_0 : Canonical s4_0 := by
  intro i
  fin_cases i <;> decide
#print axioms canon4_0
def s4_23 : State := Array.make 16#usize [1509501854#u32,1054326288#u32,990027500#u32,639862859#u32,434148632#u32,2026900882#u32,821792967#u32,1955070469#u32,2126048206#u32,1654414616#u32,1959107133#u32,943087239#u32,609987601#u32,1346814918#u32,58140128#u32,1000734734#u32]
theorem lift4_23 : liftA (K := PV_RunJoin_FixtureRecords.M) s4_23 = PV_RunJoin_FixtureHashModel.s_4_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift4_23
theorem canon4_23 : Canonical s4_23 := by
  intro i
  fin_cases i <;> decide
#print axioms canon4_23
def s5_0 : State := Array.make 16#usize [1509501955#u32,1054326406#u32,990027635#u32,639863011#u32,434148801#u32,2026901068#u32,821793170#u32,1955070689#u32,2126048206#u32,1654414616#u32,1959107133#u32,943087239#u32,609987601#u32,1346814918#u32,58140128#u32,1000734734#u32]
theorem lift5_0 : liftA (K := PV_RunJoin_FixtureRecords.M) s5_0 = PV_RunJoin_FixtureHashModel.s_5_0 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift5_0
theorem canon5_0 : Canonical s5_0 := by
  intro i
  fin_cases i <;> decide
#print axioms canon5_0
def s5_23 : State := Array.make 16#usize [8526811#u32,109678668#u32,1639079956#u32,402852#u32,1893371776#u32,347120802#u32,331397657#u32,1970188241#u32,915703419#u32,940187825#u32,1218577884#u32,1412233520#u32,244420717#u32,1756009899#u32,487108249#u32,1028913813#u32]
theorem lift5_23 : liftA (K := PV_RunJoin_FixtureRecords.M) s5_23 = PV_RunJoin_FixtureHashModel.s_5_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms lift5_23
theorem canon5_23 : Canonical s5_23 := by
  intro i
  fin_cases i <;> decide
#print axioms canon5_23
end R1Z.PV_RunJoin_NullifierData17
