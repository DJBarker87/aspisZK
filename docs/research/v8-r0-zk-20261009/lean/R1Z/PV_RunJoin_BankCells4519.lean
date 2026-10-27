import R1Z.PV_RunJoin_BankCertificate19
import R1Z.PV_RunJoin_ValidatorGroup4319
import R1Z.PV_RunJoin_ValidatorGroup4619
import R1Z.PV_RunJoin_ValidatorGroup4919
import R1Z.PV_RunJoin_ValidatorGroup5219
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell4519
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [650311058#u32,434968666#u32,41653783#u32,849815005#u32,1944690526#u32,1561873308#u32,545397838#u32,336751789#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,803983598#u32]
def a1 : State := Array.make 16#usize [650311058#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,803983598#u32]
def a2 : State := Array.make 16#usize [650311058#u32,434968666#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,803983598#u32]
def a3 : State := Array.make 16#usize [650311058#u32,434968666#u32,41653783#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,803983598#u32]
def a4 : State := Array.make 16#usize [650311058#u32,434968666#u32,41653783#u32,849815005#u32,0#u32,0#u32,0#u32,0#u32,1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,803983598#u32]
def a5 : State := Array.make 16#usize [650311058#u32,434968666#u32,41653783#u32,849815005#u32,1944690526#u32,0#u32,0#u32,0#u32,1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,803983598#u32]
def a6 : State := Array.make 16#usize [650311058#u32,434968666#u32,41653783#u32,849815005#u32,1944690526#u32,1561873308#u32,0#u32,0#u32,1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,803983598#u32]
def a7 : State := Array.make 16#usize [650311058#u32,434968666#u32,41653783#u32,849815005#u32,1944690526#u32,1561873308#u32,545397838#u32,0#u32,1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,803983598#u32]
def a8 : State := Array.make 16#usize [650311058#u32,434968666#u32,41653783#u32,849815005#u32,1944690526#u32,1561873308#u32,545397838#u32,336751789#u32,1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,803983598#u32]
def absorbed (n : Nat) : State := match n with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8
  | _ => a8
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorCell4519.s0
  | 1 => PV_RunJoin_ValidatorCell4519.s3
  | 2 => PV_RunJoin_ValidatorCell4519.s5
  | 3 => PV_RunJoin_ValidatorCell4519.s7
  | 4 => PV_RunJoin_ValidatorCell4519.s9
  | 5 => PV_RunJoin_ValidatorCell4519.s11
  | 6 => PV_RunJoin_ValidatorCell4519.s13
  | 7 => PV_RunJoin_ValidatorCell4519.s15
  | 8 => PV_RunJoin_ValidatorCell4519.s17
  | 9 => PV_RunJoin_ValidatorCell4519.s19
  | 10 => PV_RunJoin_ValidatorCell4519.s21
  | 11 => PV_RunJoin_ValidatorCell4519.s23
  | _ => PV_RunJoin_ValidatorCell4519.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨650311058#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨434968666#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨41653783#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨849815005#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1944690526#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1561873308#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨545397838#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨336751789#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell4519.s2,PV_RunJoin_ValidatorCell4519.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell4519.s4,PV_RunJoin_ValidatorCell4519.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell4519.s6,PV_RunJoin_ValidatorCell4519.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell4519.s8,PV_RunJoin_ValidatorCell4519.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell4519.s10,PV_RunJoin_ValidatorCell4519.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell4519.s12,PV_RunJoin_ValidatorCell4519.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell4519.s14,PV_RunJoin_ValidatorCell4519.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell4519.s16,PV_RunJoin_ValidatorCell4519.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell4519.s18,PV_RunJoin_ValidatorCell4519.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell4519.s20,PV_RunJoin_ValidatorCell4519.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell4519.s22,PV_RunJoin_ValidatorCell4519.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell4519

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell4619
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1736209514#u32,234715035#u32,487763438#u32,1135092556#u32,1921147183#u32,568436335#u32,1137697966#u32,357096408#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,1657047221#u32]
def a1 : State := Array.make 16#usize [1736209514#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,1657047221#u32]
def a2 : State := Array.make 16#usize [1736209514#u32,234715035#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,1657047221#u32]
def a3 : State := Array.make 16#usize [1736209514#u32,234715035#u32,487763438#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,1657047221#u32]
def a4 : State := Array.make 16#usize [1736209514#u32,234715035#u32,487763438#u32,1135092556#u32,0#u32,0#u32,0#u32,0#u32,1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,1657047221#u32]
def a5 : State := Array.make 16#usize [1736209514#u32,234715035#u32,487763438#u32,1135092556#u32,1921147183#u32,0#u32,0#u32,0#u32,1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,1657047221#u32]
def a6 : State := Array.make 16#usize [1736209514#u32,234715035#u32,487763438#u32,1135092556#u32,1921147183#u32,568436335#u32,0#u32,0#u32,1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,1657047221#u32]
def a7 : State := Array.make 16#usize [1736209514#u32,234715035#u32,487763438#u32,1135092556#u32,1921147183#u32,568436335#u32,1137697966#u32,0#u32,1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,1657047221#u32]
def a8 : State := Array.make 16#usize [1736209514#u32,234715035#u32,487763438#u32,1135092556#u32,1921147183#u32,568436335#u32,1137697966#u32,357096408#u32,1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,1657047221#u32]
def absorbed (n : Nat) : State := match n with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8
  | _ => a8
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorCell4619.s0
  | 1 => PV_RunJoin_ValidatorCell4619.s3
  | 2 => PV_RunJoin_ValidatorCell4619.s5
  | 3 => PV_RunJoin_ValidatorCell4619.s7
  | 4 => PV_RunJoin_ValidatorCell4619.s9
  | 5 => PV_RunJoin_ValidatorCell4619.s11
  | 6 => PV_RunJoin_ValidatorCell4619.s13
  | 7 => PV_RunJoin_ValidatorCell4619.s15
  | 8 => PV_RunJoin_ValidatorCell4619.s17
  | 9 => PV_RunJoin_ValidatorCell4619.s19
  | 10 => PV_RunJoin_ValidatorCell4619.s21
  | 11 => PV_RunJoin_ValidatorCell4619.s23
  | _ => PV_RunJoin_ValidatorCell4619.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1736209514#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨234715035#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨487763438#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1135092556#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1921147183#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨568436335#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1137697966#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨357096408#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell4619.s2,PV_RunJoin_ValidatorCell4619.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell4619.s4,PV_RunJoin_ValidatorCell4619.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell4619.s6,PV_RunJoin_ValidatorCell4619.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell4619.s8,PV_RunJoin_ValidatorCell4619.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell4619.s10,PV_RunJoin_ValidatorCell4619.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell4619.s12,PV_RunJoin_ValidatorCell4619.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell4619.s14,PV_RunJoin_ValidatorCell4619.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell4619.s16,PV_RunJoin_ValidatorCell4619.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell4619.s18,PV_RunJoin_ValidatorCell4619.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell4619.s20,PV_RunJoin_ValidatorCell4619.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell4619.s22,PV_RunJoin_ValidatorCell4619.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell4619

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell4719
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [874162269#u32,1451641120#u32,2103371390#u32,1001754857#u32,1905791956#u32,1847859879#u32,128353993#u32,1497851806#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
def a1 : State := Array.make 16#usize [874162269#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
def a2 : State := Array.make 16#usize [874162269#u32,1451641120#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
def a3 : State := Array.make 16#usize [874162269#u32,1451641120#u32,2103371390#u32,0#u32,0#u32,0#u32,0#u32,0#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
def a4 : State := Array.make 16#usize [874162269#u32,1451641120#u32,2103371390#u32,1001754857#u32,0#u32,0#u32,0#u32,0#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
def a5 : State := Array.make 16#usize [874162269#u32,1451641120#u32,2103371390#u32,1001754857#u32,1905791956#u32,0#u32,0#u32,0#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
def a6 : State := Array.make 16#usize [874162269#u32,1451641120#u32,2103371390#u32,1001754857#u32,1905791956#u32,1847859879#u32,0#u32,0#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
def a7 : State := Array.make 16#usize [874162269#u32,1451641120#u32,2103371390#u32,1001754857#u32,1905791956#u32,1847859879#u32,128353993#u32,0#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
def a8 : State := Array.make 16#usize [874162269#u32,1451641120#u32,2103371390#u32,1001754857#u32,1905791956#u32,1847859879#u32,128353993#u32,1497851806#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
def absorbed (n : Nat) : State := match n with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8
  | _ => a8
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorCell4719.s0
  | 1 => PV_RunJoin_ValidatorCell4719.s3
  | 2 => PV_RunJoin_ValidatorCell4719.s5
  | 3 => PV_RunJoin_ValidatorCell4719.s7
  | 4 => PV_RunJoin_ValidatorCell4719.s9
  | 5 => PV_RunJoin_ValidatorCell4719.s11
  | 6 => PV_RunJoin_ValidatorCell4719.s13
  | 7 => PV_RunJoin_ValidatorCell4719.s15
  | 8 => PV_RunJoin_ValidatorCell4719.s17
  | 9 => PV_RunJoin_ValidatorCell4719.s19
  | 10 => PV_RunJoin_ValidatorCell4719.s21
  | 11 => PV_RunJoin_ValidatorCell4719.s23
  | _ => PV_RunJoin_ValidatorCell4719.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨874162269#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1451641120#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2103371390#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1001754857#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1905791956#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1847859879#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨128353993#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1497851806#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell4719.s2,PV_RunJoin_ValidatorCell4719.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell4719.s4,PV_RunJoin_ValidatorCell4719.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell4719.s6,PV_RunJoin_ValidatorCell4719.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell4719.s8,PV_RunJoin_ValidatorCell4719.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell4719.s10,PV_RunJoin_ValidatorCell4719.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell4719.s12,PV_RunJoin_ValidatorCell4719.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell4719.s14,PV_RunJoin_ValidatorCell4719.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell4719.s16,PV_RunJoin_ValidatorCell4719.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell4719.s18,PV_RunJoin_ValidatorCell4719.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell4719.s20,PV_RunJoin_ValidatorCell4719.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell4719.s22,PV_RunJoin_ValidatorCell4719.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell4719

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell4819
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [779813195#u32,274765226#u32,1694692007#u32,261106508#u32,380728998#u32,546229929#u32,1098356305#u32,1560230773#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
def a1 : State := Array.make 16#usize [779813195#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
def a2 : State := Array.make 16#usize [779813195#u32,274765226#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
def a3 : State := Array.make 16#usize [779813195#u32,274765226#u32,1694692007#u32,0#u32,0#u32,0#u32,0#u32,0#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
def a4 : State := Array.make 16#usize [779813195#u32,274765226#u32,1694692007#u32,261106508#u32,0#u32,0#u32,0#u32,0#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
def a5 : State := Array.make 16#usize [779813195#u32,274765226#u32,1694692007#u32,261106508#u32,380728998#u32,0#u32,0#u32,0#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
def a6 : State := Array.make 16#usize [779813195#u32,274765226#u32,1694692007#u32,261106508#u32,380728998#u32,546229929#u32,0#u32,0#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
def a7 : State := Array.make 16#usize [779813195#u32,274765226#u32,1694692007#u32,261106508#u32,380728998#u32,546229929#u32,1098356305#u32,0#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
def a8 : State := Array.make 16#usize [779813195#u32,274765226#u32,1694692007#u32,261106508#u32,380728998#u32,546229929#u32,1098356305#u32,1560230773#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
def absorbed (n : Nat) : State := match n with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8
  | _ => a8
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorCell4819.s0
  | 1 => PV_RunJoin_ValidatorCell4819.s3
  | 2 => PV_RunJoin_ValidatorCell4819.s5
  | 3 => PV_RunJoin_ValidatorCell4819.s7
  | 4 => PV_RunJoin_ValidatorCell4819.s9
  | 5 => PV_RunJoin_ValidatorCell4819.s11
  | 6 => PV_RunJoin_ValidatorCell4819.s13
  | 7 => PV_RunJoin_ValidatorCell4819.s15
  | 8 => PV_RunJoin_ValidatorCell4819.s17
  | 9 => PV_RunJoin_ValidatorCell4819.s19
  | 10 => PV_RunJoin_ValidatorCell4819.s21
  | 11 => PV_RunJoin_ValidatorCell4819.s23
  | _ => PV_RunJoin_ValidatorCell4819.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨779813195#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨274765226#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1694692007#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨261106508#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨380728998#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨546229929#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1098356305#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1560230773#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell4819.s2,PV_RunJoin_ValidatorCell4819.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell4819.s4,PV_RunJoin_ValidatorCell4819.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell4819.s6,PV_RunJoin_ValidatorCell4819.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell4819.s8,PV_RunJoin_ValidatorCell4819.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell4819.s10,PV_RunJoin_ValidatorCell4819.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell4819.s12,PV_RunJoin_ValidatorCell4819.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell4819.s14,PV_RunJoin_ValidatorCell4819.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell4819.s16,PV_RunJoin_ValidatorCell4819.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell4819.s18,PV_RunJoin_ValidatorCell4819.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell4819.s20,PV_RunJoin_ValidatorCell4819.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell4819.s22,PV_RunJoin_ValidatorCell4819.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell4819

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell4919
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [985515685#u32,670227816#u32,320139735#u32,164221359#u32,586867065#u32,504851391#u32,659699442#u32,1594817757#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
def a1 : State := Array.make 16#usize [985515685#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
def a2 : State := Array.make 16#usize [985515685#u32,670227816#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
def a3 : State := Array.make 16#usize [985515685#u32,670227816#u32,320139735#u32,0#u32,0#u32,0#u32,0#u32,0#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
def a4 : State := Array.make 16#usize [985515685#u32,670227816#u32,320139735#u32,164221359#u32,0#u32,0#u32,0#u32,0#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
def a5 : State := Array.make 16#usize [985515685#u32,670227816#u32,320139735#u32,164221359#u32,586867065#u32,0#u32,0#u32,0#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
def a6 : State := Array.make 16#usize [985515685#u32,670227816#u32,320139735#u32,164221359#u32,586867065#u32,504851391#u32,0#u32,0#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
def a7 : State := Array.make 16#usize [985515685#u32,670227816#u32,320139735#u32,164221359#u32,586867065#u32,504851391#u32,659699442#u32,0#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
def a8 : State := Array.make 16#usize [985515685#u32,670227816#u32,320139735#u32,164221359#u32,586867065#u32,504851391#u32,659699442#u32,1594817757#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
def absorbed (n : Nat) : State := match n with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8
  | _ => a8
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorCell4919.s0
  | 1 => PV_RunJoin_ValidatorCell4919.s3
  | 2 => PV_RunJoin_ValidatorCell4919.s5
  | 3 => PV_RunJoin_ValidatorCell4919.s7
  | 4 => PV_RunJoin_ValidatorCell4919.s9
  | 5 => PV_RunJoin_ValidatorCell4919.s11
  | 6 => PV_RunJoin_ValidatorCell4919.s13
  | 7 => PV_RunJoin_ValidatorCell4919.s15
  | 8 => PV_RunJoin_ValidatorCell4919.s17
  | 9 => PV_RunJoin_ValidatorCell4919.s19
  | 10 => PV_RunJoin_ValidatorCell4919.s21
  | 11 => PV_RunJoin_ValidatorCell4919.s23
  | _ => PV_RunJoin_ValidatorCell4919.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨985515685#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨670227816#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨320139735#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨164221359#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨586867065#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨504851391#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨659699442#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1594817757#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell4919.s2,PV_RunJoin_ValidatorCell4919.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell4919.s4,PV_RunJoin_ValidatorCell4919.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell4919.s6,PV_RunJoin_ValidatorCell4919.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell4919.s8,PV_RunJoin_ValidatorCell4919.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell4919.s10,PV_RunJoin_ValidatorCell4919.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell4919.s12,PV_RunJoin_ValidatorCell4919.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell4919.s14,PV_RunJoin_ValidatorCell4919.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell4919.s16,PV_RunJoin_ValidatorCell4919.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell4919.s18,PV_RunJoin_ValidatorCell4919.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell4919.s20,PV_RunJoin_ValidatorCell4919.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell4919.s22,PV_RunJoin_ValidatorCell4919.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell4919

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell5019
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [210048012#u32,966687588#u32,869731705#u32,823470673#u32,703197799#u32,1759368079#u32,456367603#u32,772376783#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
def a1 : State := Array.make 16#usize [210048012#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
def a2 : State := Array.make 16#usize [210048012#u32,966687588#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
def a3 : State := Array.make 16#usize [210048012#u32,966687588#u32,869731705#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
def a4 : State := Array.make 16#usize [210048012#u32,966687588#u32,869731705#u32,823470673#u32,0#u32,0#u32,0#u32,0#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
def a5 : State := Array.make 16#usize [210048012#u32,966687588#u32,869731705#u32,823470673#u32,703197799#u32,0#u32,0#u32,0#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
def a6 : State := Array.make 16#usize [210048012#u32,966687588#u32,869731705#u32,823470673#u32,703197799#u32,1759368079#u32,0#u32,0#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
def a7 : State := Array.make 16#usize [210048012#u32,966687588#u32,869731705#u32,823470673#u32,703197799#u32,1759368079#u32,456367603#u32,0#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
def a8 : State := Array.make 16#usize [210048012#u32,966687588#u32,869731705#u32,823470673#u32,703197799#u32,1759368079#u32,456367603#u32,772376783#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
def absorbed (n : Nat) : State := match n with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8
  | _ => a8
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorCell5019.s0
  | 1 => PV_RunJoin_ValidatorCell5019.s3
  | 2 => PV_RunJoin_ValidatorCell5019.s5
  | 3 => PV_RunJoin_ValidatorCell5019.s7
  | 4 => PV_RunJoin_ValidatorCell5019.s9
  | 5 => PV_RunJoin_ValidatorCell5019.s11
  | 6 => PV_RunJoin_ValidatorCell5019.s13
  | 7 => PV_RunJoin_ValidatorCell5019.s15
  | 8 => PV_RunJoin_ValidatorCell5019.s17
  | 9 => PV_RunJoin_ValidatorCell5019.s19
  | 10 => PV_RunJoin_ValidatorCell5019.s21
  | 11 => PV_RunJoin_ValidatorCell5019.s23
  | _ => PV_RunJoin_ValidatorCell5019.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨210048012#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨966687588#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨869731705#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨823470673#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨703197799#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1759368079#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨456367603#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨772376783#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell5019.s2,PV_RunJoin_ValidatorCell5019.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell5019.s4,PV_RunJoin_ValidatorCell5019.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell5019.s6,PV_RunJoin_ValidatorCell5019.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell5019.s8,PV_RunJoin_ValidatorCell5019.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell5019.s10,PV_RunJoin_ValidatorCell5019.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell5019.s12,PV_RunJoin_ValidatorCell5019.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell5019.s14,PV_RunJoin_ValidatorCell5019.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell5019.s16,PV_RunJoin_ValidatorCell5019.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell5019.s18,PV_RunJoin_ValidatorCell5019.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell5019.s20,PV_RunJoin_ValidatorCell5019.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell5019.s22,PV_RunJoin_ValidatorCell5019.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell5019

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell5119
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1483663627#u32,500119681#u32,2118402728#u32,174107570#u32,654106964#u32,85317403#u32,1579623758#u32,1770549948#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
def a1 : State := Array.make 16#usize [1483663627#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
def a2 : State := Array.make 16#usize [1483663627#u32,500119681#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
def a3 : State := Array.make 16#usize [1483663627#u32,500119681#u32,2118402728#u32,0#u32,0#u32,0#u32,0#u32,0#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
def a4 : State := Array.make 16#usize [1483663627#u32,500119681#u32,2118402728#u32,174107570#u32,0#u32,0#u32,0#u32,0#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
def a5 : State := Array.make 16#usize [1483663627#u32,500119681#u32,2118402728#u32,174107570#u32,654106964#u32,0#u32,0#u32,0#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
def a6 : State := Array.make 16#usize [1483663627#u32,500119681#u32,2118402728#u32,174107570#u32,654106964#u32,85317403#u32,0#u32,0#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
def a7 : State := Array.make 16#usize [1483663627#u32,500119681#u32,2118402728#u32,174107570#u32,654106964#u32,85317403#u32,1579623758#u32,0#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
def a8 : State := Array.make 16#usize [1483663627#u32,500119681#u32,2118402728#u32,174107570#u32,654106964#u32,85317403#u32,1579623758#u32,1770549948#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
def absorbed (n : Nat) : State := match n with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8
  | _ => a8
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorCell5119.s0
  | 1 => PV_RunJoin_ValidatorCell5119.s3
  | 2 => PV_RunJoin_ValidatorCell5119.s5
  | 3 => PV_RunJoin_ValidatorCell5119.s7
  | 4 => PV_RunJoin_ValidatorCell5119.s9
  | 5 => PV_RunJoin_ValidatorCell5119.s11
  | 6 => PV_RunJoin_ValidatorCell5119.s13
  | 7 => PV_RunJoin_ValidatorCell5119.s15
  | 8 => PV_RunJoin_ValidatorCell5119.s17
  | 9 => PV_RunJoin_ValidatorCell5119.s19
  | 10 => PV_RunJoin_ValidatorCell5119.s21
  | 11 => PV_RunJoin_ValidatorCell5119.s23
  | _ => PV_RunJoin_ValidatorCell5119.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1483663627#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨500119681#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2118402728#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨174107570#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨654106964#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨85317403#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1579623758#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1770549948#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell5119.s2,PV_RunJoin_ValidatorCell5119.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell5119.s4,PV_RunJoin_ValidatorCell5119.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell5119.s6,PV_RunJoin_ValidatorCell5119.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell5119.s8,PV_RunJoin_ValidatorCell5119.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell5119.s10,PV_RunJoin_ValidatorCell5119.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell5119.s12,PV_RunJoin_ValidatorCell5119.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell5119.s14,PV_RunJoin_ValidatorCell5119.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell5119.s16,PV_RunJoin_ValidatorCell5119.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell5119.s18,PV_RunJoin_ValidatorCell5119.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell5119.s20,PV_RunJoin_ValidatorCell5119.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell5119.s22,PV_RunJoin_ValidatorCell5119.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell5119

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell5219
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [578338833#u32,1226544375#u32,1719735936#u32,2046596019#u32,1635531819#u32,454303639#u32,1556588950#u32,1520337232#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
def a1 : State := Array.make 16#usize [578338833#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
def a2 : State := Array.make 16#usize [578338833#u32,1226544375#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
def a3 : State := Array.make 16#usize [578338833#u32,1226544375#u32,1719735936#u32,0#u32,0#u32,0#u32,0#u32,0#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
def a4 : State := Array.make 16#usize [578338833#u32,1226544375#u32,1719735936#u32,2046596019#u32,0#u32,0#u32,0#u32,0#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
def a5 : State := Array.make 16#usize [578338833#u32,1226544375#u32,1719735936#u32,2046596019#u32,1635531819#u32,0#u32,0#u32,0#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
def a6 : State := Array.make 16#usize [578338833#u32,1226544375#u32,1719735936#u32,2046596019#u32,1635531819#u32,454303639#u32,0#u32,0#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
def a7 : State := Array.make 16#usize [578338833#u32,1226544375#u32,1719735936#u32,2046596019#u32,1635531819#u32,454303639#u32,1556588950#u32,0#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
def a8 : State := Array.make 16#usize [578338833#u32,1226544375#u32,1719735936#u32,2046596019#u32,1635531819#u32,454303639#u32,1556588950#u32,1520337232#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
def absorbed (n : Nat) : State := match n with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8
  | _ => a8
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorCell5219.s0
  | 1 => PV_RunJoin_ValidatorCell5219.s3
  | 2 => PV_RunJoin_ValidatorCell5219.s5
  | 3 => PV_RunJoin_ValidatorCell5219.s7
  | 4 => PV_RunJoin_ValidatorCell5219.s9
  | 5 => PV_RunJoin_ValidatorCell5219.s11
  | 6 => PV_RunJoin_ValidatorCell5219.s13
  | 7 => PV_RunJoin_ValidatorCell5219.s15
  | 8 => PV_RunJoin_ValidatorCell5219.s17
  | 9 => PV_RunJoin_ValidatorCell5219.s19
  | 10 => PV_RunJoin_ValidatorCell5219.s21
  | 11 => PV_RunJoin_ValidatorCell5219.s23
  | _ => PV_RunJoin_ValidatorCell5219.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨578338833#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1226544375#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1719735936#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2046596019#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1635531819#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨454303639#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1556588950#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1520337232#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell5219.s2,PV_RunJoin_ValidatorCell5219.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell5219.s4,PV_RunJoin_ValidatorCell5219.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell5219.s6,PV_RunJoin_ValidatorCell5219.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell5219.s8,PV_RunJoin_ValidatorCell5219.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell5219.s10,PV_RunJoin_ValidatorCell5219.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell5219.s12,PV_RunJoin_ValidatorCell5219.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell5219.s14,PV_RunJoin_ValidatorCell5219.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell5219.s16,PV_RunJoin_ValidatorCell5219.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell5219.s18,PV_RunJoin_ValidatorCell5219.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell5219.s20,PV_RunJoin_ValidatorCell5219.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell5219.s22,PV_RunJoin_ValidatorCell5219.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell5219

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell5319
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1033316416#u32,1871077402#u32,1557962334#u32,322514877#u32,1982083472#u32,813203847#u32,1866642001#u32,508617919#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,1001875166#u32]
def a1 : State := Array.make 16#usize [1033316416#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,1001875166#u32]
def a2 : State := Array.make 16#usize [1033316416#u32,1871077402#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,1001875166#u32]
def a3 : State := Array.make 16#usize [1033316416#u32,1871077402#u32,1557962334#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,1001875166#u32]
def a4 : State := Array.make 16#usize [1033316416#u32,1871077402#u32,1557962334#u32,322514877#u32,0#u32,0#u32,0#u32,0#u32,2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,1001875166#u32]
def a5 : State := Array.make 16#usize [1033316416#u32,1871077402#u32,1557962334#u32,322514877#u32,1982083472#u32,0#u32,0#u32,0#u32,2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,1001875166#u32]
def a6 : State := Array.make 16#usize [1033316416#u32,1871077402#u32,1557962334#u32,322514877#u32,1982083472#u32,813203847#u32,0#u32,0#u32,2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,1001875166#u32]
def a7 : State := Array.make 16#usize [1033316416#u32,1871077402#u32,1557962334#u32,322514877#u32,1982083472#u32,813203847#u32,1866642001#u32,0#u32,2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,1001875166#u32]
def a8 : State := Array.make 16#usize [1033316416#u32,1871077402#u32,1557962334#u32,322514877#u32,1982083472#u32,813203847#u32,1866642001#u32,508617919#u32,2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,1001875166#u32]
def absorbed (n : Nat) : State := match n with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8
  | _ => a8
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorCell5319.s0
  | 1 => PV_RunJoin_ValidatorCell5319.s3
  | 2 => PV_RunJoin_ValidatorCell5319.s5
  | 3 => PV_RunJoin_ValidatorCell5319.s7
  | 4 => PV_RunJoin_ValidatorCell5319.s9
  | 5 => PV_RunJoin_ValidatorCell5319.s11
  | 6 => PV_RunJoin_ValidatorCell5319.s13
  | 7 => PV_RunJoin_ValidatorCell5319.s15
  | 8 => PV_RunJoin_ValidatorCell5319.s17
  | 9 => PV_RunJoin_ValidatorCell5319.s19
  | 10 => PV_RunJoin_ValidatorCell5319.s21
  | 11 => PV_RunJoin_ValidatorCell5319.s23
  | _ => PV_RunJoin_ValidatorCell5319.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1033316416#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1871077402#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1557962334#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨322514877#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1982083472#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨813203847#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1866642001#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨508617919#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell5319.s2,PV_RunJoin_ValidatorCell5319.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell5319.s4,PV_RunJoin_ValidatorCell5319.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell5319.s6,PV_RunJoin_ValidatorCell5319.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell5319.s8,PV_RunJoin_ValidatorCell5319.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell5319.s10,PV_RunJoin_ValidatorCell5319.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell5319.s12,PV_RunJoin_ValidatorCell5319.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell5319.s14,PV_RunJoin_ValidatorCell5319.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell5319.s16,PV_RunJoin_ValidatorCell5319.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell5319.s18,PV_RunJoin_ValidatorCell5319.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell5319.s20,PV_RunJoin_ValidatorCell5319.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell5319.s22,PV_RunJoin_ValidatorCell5319.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell5319
