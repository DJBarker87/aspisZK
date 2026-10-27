import R1Z.PV_RunJoin_BankCertificate19
import R1Z.PV_RunJoin_ValidatorGroup3419
import R1Z.PV_RunJoin_ValidatorGroup3719
import R1Z.PV_RunJoin_ValidatorGroup4019
import R1Z.PV_RunJoin_ValidatorGroup4319
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell3619
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [701#u32,718#u32,735#u32,752#u32,769#u32,786#u32,803#u32,820#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a1 : State := Array.make 16#usize [701#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a2 : State := Array.make 16#usize [701#u32,718#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a3 : State := Array.make 16#usize [701#u32,718#u32,735#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a4 : State := Array.make 16#usize [701#u32,718#u32,735#u32,752#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a5 : State := Array.make 16#usize [701#u32,718#u32,735#u32,752#u32,769#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a6 : State := Array.make 16#usize [701#u32,718#u32,735#u32,752#u32,769#u32,786#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a7 : State := Array.make 16#usize [701#u32,718#u32,735#u32,752#u32,769#u32,786#u32,803#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a8 : State := Array.make 16#usize [701#u32,718#u32,735#u32,752#u32,769#u32,786#u32,803#u32,820#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
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
  | 0 => PV_RunJoin_ValidatorCell3619.s0
  | 1 => PV_RunJoin_ValidatorCell3619.s3
  | 2 => PV_RunJoin_ValidatorCell3619.s5
  | 3 => PV_RunJoin_ValidatorCell3619.s7
  | 4 => PV_RunJoin_ValidatorCell3619.s9
  | 5 => PV_RunJoin_ValidatorCell3619.s11
  | 6 => PV_RunJoin_ValidatorCell3619.s13
  | 7 => PV_RunJoin_ValidatorCell3619.s15
  | 8 => PV_RunJoin_ValidatorCell3619.s17
  | 9 => PV_RunJoin_ValidatorCell3619.s19
  | 10 => PV_RunJoin_ValidatorCell3619.s21
  | 11 => PV_RunJoin_ValidatorCell3619.s23
  | _ => PV_RunJoin_ValidatorCell3619.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨701#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨718#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨735#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨752#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨769#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨786#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨803#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨820#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell3619.s2,PV_RunJoin_ValidatorCell3619.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell3619.s4,PV_RunJoin_ValidatorCell3619.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell3619.s6,PV_RunJoin_ValidatorCell3619.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell3619.s8,PV_RunJoin_ValidatorCell3619.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell3619.s10,PV_RunJoin_ValidatorCell3619.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell3619.s12,PV_RunJoin_ValidatorCell3619.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell3619.s14,PV_RunJoin_ValidatorCell3619.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell3619.s16,PV_RunJoin_ValidatorCell3619.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell3619.s18,PV_RunJoin_ValidatorCell3619.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell3619.s20,PV_RunJoin_ValidatorCell3619.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell3619.s22,PV_RunJoin_ValidatorCell3619.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell3619

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell3719
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [750#u32,77#u32,801#u32,818#u32,835#u32,852#u32,869#u32,886#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [546281967#u32,1559728043#u32,480221020#u32,1137562093#u32,1073380732#u32,946947524#u32,2130673944#u32,272035770#u32,626572232#u32,2011772409#u32,1574981444#u32,383529292#u32,998577542#u32,1416076312#u32,2063726935#u32,1857484848#u32]
def a1 : State := Array.make 16#usize [546282717#u32,1559728043#u32,480221020#u32,1137562093#u32,1073380732#u32,946947524#u32,2130673944#u32,272035770#u32,626572232#u32,2011772409#u32,1574981444#u32,383529292#u32,998577542#u32,1416076312#u32,2063726935#u32,1857484848#u32]
def a2 : State := Array.make 16#usize [546282717#u32,1559728120#u32,480221020#u32,1137562093#u32,1073380732#u32,946947524#u32,2130673944#u32,272035770#u32,626572232#u32,2011772409#u32,1574981444#u32,383529292#u32,998577542#u32,1416076312#u32,2063726935#u32,1857484848#u32]
def a3 : State := Array.make 16#usize [546282717#u32,1559728120#u32,480221821#u32,1137562093#u32,1073380732#u32,946947524#u32,2130673944#u32,272035770#u32,626572232#u32,2011772409#u32,1574981444#u32,383529292#u32,998577542#u32,1416076312#u32,2063726935#u32,1857484848#u32]
def a4 : State := Array.make 16#usize [546282717#u32,1559728120#u32,480221821#u32,1137562911#u32,1073380732#u32,946947524#u32,2130673944#u32,272035770#u32,626572232#u32,2011772409#u32,1574981444#u32,383529292#u32,998577542#u32,1416076312#u32,2063726935#u32,1857484848#u32]
def a5 : State := Array.make 16#usize [546282717#u32,1559728120#u32,480221821#u32,1137562911#u32,1073381567#u32,946947524#u32,2130673944#u32,272035770#u32,626572232#u32,2011772409#u32,1574981444#u32,383529292#u32,998577542#u32,1416076312#u32,2063726935#u32,1857484848#u32]
def a6 : State := Array.make 16#usize [546282717#u32,1559728120#u32,480221821#u32,1137562911#u32,1073381567#u32,946948376#u32,2130673944#u32,272035770#u32,626572232#u32,2011772409#u32,1574981444#u32,383529292#u32,998577542#u32,1416076312#u32,2063726935#u32,1857484848#u32]
def a7 : State := Array.make 16#usize [546282717#u32,1559728120#u32,480221821#u32,1137562911#u32,1073381567#u32,946948376#u32,2130674813#u32,272035770#u32,626572232#u32,2011772409#u32,1574981444#u32,383529292#u32,998577542#u32,1416076312#u32,2063726935#u32,1857484848#u32]
def a8 : State := Array.make 16#usize [546282717#u32,1559728120#u32,480221821#u32,1137562911#u32,1073381567#u32,946948376#u32,2130674813#u32,272036656#u32,626572232#u32,2011772409#u32,1574981444#u32,383529292#u32,998577542#u32,1416076312#u32,2063726935#u32,1857484848#u32]
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
  | 0 => PV_RunJoin_ValidatorCell3719.s0
  | 1 => PV_RunJoin_ValidatorCell3719.s3
  | 2 => PV_RunJoin_ValidatorCell3719.s5
  | 3 => PV_RunJoin_ValidatorCell3719.s7
  | 4 => PV_RunJoin_ValidatorCell3719.s9
  | 5 => PV_RunJoin_ValidatorCell3719.s11
  | 6 => PV_RunJoin_ValidatorCell3719.s13
  | 7 => PV_RunJoin_ValidatorCell3719.s15
  | 8 => PV_RunJoin_ValidatorCell3719.s17
  | 9 => PV_RunJoin_ValidatorCell3719.s19
  | 10 => PV_RunJoin_ValidatorCell3719.s21
  | 11 => PV_RunJoin_ValidatorCell3719.s23
  | _ => PV_RunJoin_ValidatorCell3719.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨546282717#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1559728120#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨480221821#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1137562911#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1073381567#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨946948376#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2130674813#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨272036656#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell3719.s2,PV_RunJoin_ValidatorCell3719.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell3719.s4,PV_RunJoin_ValidatorCell3719.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell3719.s6,PV_RunJoin_ValidatorCell3719.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell3719.s8,PV_RunJoin_ValidatorCell3719.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell3719.s10,PV_RunJoin_ValidatorCell3719.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell3719.s12,PV_RunJoin_ValidatorCell3719.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell3719.s14,PV_RunJoin_ValidatorCell3719.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell3719.s16,PV_RunJoin_ValidatorCell3719.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell3719.s18,PV_RunJoin_ValidatorCell3719.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell3719.s20,PV_RunJoin_ValidatorCell3719.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell3719.s22,PV_RunJoin_ValidatorCell3719.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell3719

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell3819
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [903#u32,920#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [638675206#u32,689885017#u32,1472415125#u32,637785328#u32,1472361768#u32,221366601#u32,1844779220#u32,537939092#u32,1547365258#u32,718050531#u32,1328510456#u32,2085095689#u32,1179308156#u32,93647966#u32,1087751576#u32,1764312209#u32]
def a1 : State := Array.make 16#usize [638676109#u32,689885017#u32,1472415125#u32,637785328#u32,1472361768#u32,221366601#u32,1844779220#u32,537939092#u32,1547365258#u32,718050531#u32,1328510456#u32,2085095689#u32,1179308156#u32,93647966#u32,1087751576#u32,1764312209#u32]
def a2 : State := Array.make 16#usize [638676109#u32,689885937#u32,1472415125#u32,637785328#u32,1472361768#u32,221366601#u32,1844779220#u32,537939092#u32,1547365258#u32,718050531#u32,1328510456#u32,2085095689#u32,1179308156#u32,93647966#u32,1087751576#u32,1764312209#u32]
def a3 : State := Array.make 16#usize [638676109#u32,689885937#u32,1472415125#u32,637785328#u32,1472361768#u32,221366601#u32,1844779220#u32,537939092#u32,1547365258#u32,718050531#u32,1328510456#u32,2085095689#u32,1179308156#u32,93647966#u32,1087751576#u32,1764312209#u32]
def a4 : State := Array.make 16#usize [638676109#u32,689885937#u32,1472415125#u32,637785328#u32,1472361768#u32,221366601#u32,1844779220#u32,537939092#u32,1547365258#u32,718050531#u32,1328510456#u32,2085095689#u32,1179308156#u32,93647966#u32,1087751576#u32,1764312209#u32]
def a5 : State := Array.make 16#usize [638676109#u32,689885937#u32,1472415125#u32,637785328#u32,1472361768#u32,221366601#u32,1844779220#u32,537939092#u32,1547365258#u32,718050531#u32,1328510456#u32,2085095689#u32,1179308156#u32,93647966#u32,1087751576#u32,1764312209#u32]
def a6 : State := Array.make 16#usize [638676109#u32,689885937#u32,1472415125#u32,637785328#u32,1472361768#u32,221366601#u32,1844779220#u32,537939092#u32,1547365258#u32,718050531#u32,1328510456#u32,2085095689#u32,1179308156#u32,93647966#u32,1087751576#u32,1764312209#u32]
def a7 : State := Array.make 16#usize [638676109#u32,689885937#u32,1472415125#u32,637785328#u32,1472361768#u32,221366601#u32,1844779220#u32,537939092#u32,1547365258#u32,718050531#u32,1328510456#u32,2085095689#u32,1179308156#u32,93647966#u32,1087751576#u32,1764312209#u32]
def a8 : State := Array.make 16#usize [638676109#u32,689885937#u32,1472415125#u32,637785328#u32,1472361768#u32,221366601#u32,1844779220#u32,537939092#u32,1547365258#u32,718050531#u32,1328510456#u32,2085095689#u32,1179308156#u32,93647966#u32,1087751576#u32,1764312209#u32]
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
  | 0 => PV_RunJoin_ValidatorCell3819.s0
  | 1 => PV_RunJoin_ValidatorCell3819.s3
  | 2 => PV_RunJoin_ValidatorCell3819.s5
  | 3 => PV_RunJoin_ValidatorCell3819.s7
  | 4 => PV_RunJoin_ValidatorCell3819.s9
  | 5 => PV_RunJoin_ValidatorCell3819.s11
  | 6 => PV_RunJoin_ValidatorCell3819.s13
  | 7 => PV_RunJoin_ValidatorCell3819.s15
  | 8 => PV_RunJoin_ValidatorCell3819.s17
  | 9 => PV_RunJoin_ValidatorCell3819.s19
  | 10 => PV_RunJoin_ValidatorCell3819.s21
  | 11 => PV_RunJoin_ValidatorCell3819.s23
  | _ => PV_RunJoin_ValidatorCell3819.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨638676109#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨689885937#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1472415125#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨637785328#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1472361768#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨221366601#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1844779220#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨537939092#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell3819.s2,PV_RunJoin_ValidatorCell3819.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell3819.s4,PV_RunJoin_ValidatorCell3819.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell3819.s6,PV_RunJoin_ValidatorCell3819.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell3819.s8,PV_RunJoin_ValidatorCell3819.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell3819.s10,PV_RunJoin_ValidatorCell3819.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell3819.s12,PV_RunJoin_ValidatorCell3819.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell3819.s14,PV_RunJoin_ValidatorCell3819.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell3819.s16,PV_RunJoin_ValidatorCell3819.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell3819.s18,PV_RunJoin_ValidatorCell3819.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell3819.s20,PV_RunJoin_ValidatorCell3819.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell3819.s22,PV_RunJoin_ValidatorCell3819.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell3819

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell3919
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1443258150#u32,390107157#u32,739124880#u32,1925983251#u32,420127778#u32,800761649#u32,949547039#u32,74873928#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,109581603#u32,2018382657#u32,1175266929#u32,551563770#u32,389056008#u32,563172097#u32,1431420963#u32,1446980050#u32]
def a1 : State := Array.make 16#usize [1443258150#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,109581603#u32,2018382657#u32,1175266929#u32,551563770#u32,389056008#u32,563172097#u32,1431420963#u32,1446980050#u32]
def a2 : State := Array.make 16#usize [1443258150#u32,390107157#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,109581603#u32,2018382657#u32,1175266929#u32,551563770#u32,389056008#u32,563172097#u32,1431420963#u32,1446980050#u32]
def a3 : State := Array.make 16#usize [1443258150#u32,390107157#u32,739124880#u32,0#u32,0#u32,0#u32,0#u32,0#u32,109581603#u32,2018382657#u32,1175266929#u32,551563770#u32,389056008#u32,563172097#u32,1431420963#u32,1446980050#u32]
def a4 : State := Array.make 16#usize [1443258150#u32,390107157#u32,739124880#u32,1925983251#u32,0#u32,0#u32,0#u32,0#u32,109581603#u32,2018382657#u32,1175266929#u32,551563770#u32,389056008#u32,563172097#u32,1431420963#u32,1446980050#u32]
def a5 : State := Array.make 16#usize [1443258150#u32,390107157#u32,739124880#u32,1925983251#u32,420127778#u32,0#u32,0#u32,0#u32,109581603#u32,2018382657#u32,1175266929#u32,551563770#u32,389056008#u32,563172097#u32,1431420963#u32,1446980050#u32]
def a6 : State := Array.make 16#usize [1443258150#u32,390107157#u32,739124880#u32,1925983251#u32,420127778#u32,800761649#u32,0#u32,0#u32,109581603#u32,2018382657#u32,1175266929#u32,551563770#u32,389056008#u32,563172097#u32,1431420963#u32,1446980050#u32]
def a7 : State := Array.make 16#usize [1443258150#u32,390107157#u32,739124880#u32,1925983251#u32,420127778#u32,800761649#u32,949547039#u32,0#u32,109581603#u32,2018382657#u32,1175266929#u32,551563770#u32,389056008#u32,563172097#u32,1431420963#u32,1446980050#u32]
def a8 : State := Array.make 16#usize [1443258150#u32,390107157#u32,739124880#u32,1925983251#u32,420127778#u32,800761649#u32,949547039#u32,74873928#u32,109581603#u32,2018382657#u32,1175266929#u32,551563770#u32,389056008#u32,563172097#u32,1431420963#u32,1446980050#u32]
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
  | 0 => PV_RunJoin_ValidatorCell3919.s0
  | 1 => PV_RunJoin_ValidatorCell3919.s3
  | 2 => PV_RunJoin_ValidatorCell3919.s5
  | 3 => PV_RunJoin_ValidatorCell3919.s7
  | 4 => PV_RunJoin_ValidatorCell3919.s9
  | 5 => PV_RunJoin_ValidatorCell3919.s11
  | 6 => PV_RunJoin_ValidatorCell3919.s13
  | 7 => PV_RunJoin_ValidatorCell3919.s15
  | 8 => PV_RunJoin_ValidatorCell3919.s17
  | 9 => PV_RunJoin_ValidatorCell3919.s19
  | 10 => PV_RunJoin_ValidatorCell3919.s21
  | 11 => PV_RunJoin_ValidatorCell3919.s23
  | _ => PV_RunJoin_ValidatorCell3919.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1443258150#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨390107157#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨739124880#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1925983251#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨420127778#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨800761649#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨949547039#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨74873928#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell3919.s2,PV_RunJoin_ValidatorCell3919.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell3919.s4,PV_RunJoin_ValidatorCell3919.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell3919.s6,PV_RunJoin_ValidatorCell3919.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell3919.s8,PV_RunJoin_ValidatorCell3919.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell3919.s10,PV_RunJoin_ValidatorCell3919.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell3919.s12,PV_RunJoin_ValidatorCell3919.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell3919.s14,PV_RunJoin_ValidatorCell3919.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell3919.s16,PV_RunJoin_ValidatorCell3919.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell3919.s18,PV_RunJoin_ValidatorCell3919.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell3919.s20,PV_RunJoin_ValidatorCell3919.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell3919.s22,PV_RunJoin_ValidatorCell3919.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell3919

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell4019
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [263935107#u32,2015801952#u32,2126421827#u32,1338328324#u32,66681051#u32,462846977#u32,1805190326#u32,1770497381#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095962629#u32]
def a1 : State := Array.make 16#usize [263935107#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095962629#u32]
def a2 : State := Array.make 16#usize [263935107#u32,2015801952#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095962629#u32]
def a3 : State := Array.make 16#usize [263935107#u32,2015801952#u32,2126421827#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095962629#u32]
def a4 : State := Array.make 16#usize [263935107#u32,2015801952#u32,2126421827#u32,1338328324#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095962629#u32]
def a5 : State := Array.make 16#usize [263935107#u32,2015801952#u32,2126421827#u32,1338328324#u32,66681051#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095962629#u32]
def a6 : State := Array.make 16#usize [263935107#u32,2015801952#u32,2126421827#u32,1338328324#u32,66681051#u32,462846977#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095962629#u32]
def a7 : State := Array.make 16#usize [263935107#u32,2015801952#u32,2126421827#u32,1338328324#u32,66681051#u32,462846977#u32,1805190326#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095962629#u32]
def a8 : State := Array.make 16#usize [263935107#u32,2015801952#u32,2126421827#u32,1338328324#u32,66681051#u32,462846977#u32,1805190326#u32,1770497381#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095962629#u32]
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
  | 0 => PV_RunJoin_ValidatorCell4019.s0
  | 1 => PV_RunJoin_ValidatorCell4019.s3
  | 2 => PV_RunJoin_ValidatorCell4019.s5
  | 3 => PV_RunJoin_ValidatorCell4019.s7
  | 4 => PV_RunJoin_ValidatorCell4019.s9
  | 5 => PV_RunJoin_ValidatorCell4019.s11
  | 6 => PV_RunJoin_ValidatorCell4019.s13
  | 7 => PV_RunJoin_ValidatorCell4019.s15
  | 8 => PV_RunJoin_ValidatorCell4019.s17
  | 9 => PV_RunJoin_ValidatorCell4019.s19
  | 10 => PV_RunJoin_ValidatorCell4019.s21
  | 11 => PV_RunJoin_ValidatorCell4019.s23
  | _ => PV_RunJoin_ValidatorCell4019.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨263935107#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2015801952#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2126421827#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1338328324#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨66681051#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨462846977#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1805190326#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1770497381#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell4019.s2,PV_RunJoin_ValidatorCell4019.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell4019.s4,PV_RunJoin_ValidatorCell4019.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell4019.s6,PV_RunJoin_ValidatorCell4019.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell4019.s8,PV_RunJoin_ValidatorCell4019.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell4019.s10,PV_RunJoin_ValidatorCell4019.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell4019.s12,PV_RunJoin_ValidatorCell4019.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell4019.s14,PV_RunJoin_ValidatorCell4019.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell4019.s16,PV_RunJoin_ValidatorCell4019.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell4019.s18,PV_RunJoin_ValidatorCell4019.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell4019.s20,PV_RunJoin_ValidatorCell4019.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell4019.s22,PV_RunJoin_ValidatorCell4019.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell4019

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell4119
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1134794151#u32,415789335#u32,111944968#u32,1818281472#u32,628958070#u32,505282998#u32,905808425#u32,2134856457#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,103505714#u32]
def a1 : State := Array.make 16#usize [1134794151#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,103505714#u32]
def a2 : State := Array.make 16#usize [1134794151#u32,415789335#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,103505714#u32]
def a3 : State := Array.make 16#usize [1134794151#u32,415789335#u32,111944968#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,103505714#u32]
def a4 : State := Array.make 16#usize [1134794151#u32,415789335#u32,111944968#u32,1818281472#u32,0#u32,0#u32,0#u32,0#u32,1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,103505714#u32]
def a5 : State := Array.make 16#usize [1134794151#u32,415789335#u32,111944968#u32,1818281472#u32,628958070#u32,0#u32,0#u32,0#u32,1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,103505714#u32]
def a6 : State := Array.make 16#usize [1134794151#u32,415789335#u32,111944968#u32,1818281472#u32,628958070#u32,505282998#u32,0#u32,0#u32,1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,103505714#u32]
def a7 : State := Array.make 16#usize [1134794151#u32,415789335#u32,111944968#u32,1818281472#u32,628958070#u32,505282998#u32,905808425#u32,0#u32,1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,103505714#u32]
def a8 : State := Array.make 16#usize [1134794151#u32,415789335#u32,111944968#u32,1818281472#u32,628958070#u32,505282998#u32,905808425#u32,2134856457#u32,1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,103505714#u32]
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
  | 0 => PV_RunJoin_ValidatorCell4119.s0
  | 1 => PV_RunJoin_ValidatorCell4119.s3
  | 2 => PV_RunJoin_ValidatorCell4119.s5
  | 3 => PV_RunJoin_ValidatorCell4119.s7
  | 4 => PV_RunJoin_ValidatorCell4119.s9
  | 5 => PV_RunJoin_ValidatorCell4119.s11
  | 6 => PV_RunJoin_ValidatorCell4119.s13
  | 7 => PV_RunJoin_ValidatorCell4119.s15
  | 8 => PV_RunJoin_ValidatorCell4119.s17
  | 9 => PV_RunJoin_ValidatorCell4119.s19
  | 10 => PV_RunJoin_ValidatorCell4119.s21
  | 11 => PV_RunJoin_ValidatorCell4119.s23
  | _ => PV_RunJoin_ValidatorCell4119.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1134794151#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨415789335#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨111944968#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1818281472#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨628958070#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨505282998#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨905808425#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2134856457#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell4119.s2,PV_RunJoin_ValidatorCell4119.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell4119.s4,PV_RunJoin_ValidatorCell4119.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell4119.s6,PV_RunJoin_ValidatorCell4119.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell4119.s8,PV_RunJoin_ValidatorCell4119.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell4119.s10,PV_RunJoin_ValidatorCell4119.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell4119.s12,PV_RunJoin_ValidatorCell4119.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell4119.s14,PV_RunJoin_ValidatorCell4119.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell4119.s16,PV_RunJoin_ValidatorCell4119.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell4119.s18,PV_RunJoin_ValidatorCell4119.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell4119.s20,PV_RunJoin_ValidatorCell4119.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell4119.s22,PV_RunJoin_ValidatorCell4119.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell4119

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell4219
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1939205616#u32,641788683#u32,1281268521#u32,866499727#u32,385183050#u32,1408789791#u32,1189739305#u32,569851020#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,2134309165#u32]
def a1 : State := Array.make 16#usize [1939205616#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,2134309165#u32]
def a2 : State := Array.make 16#usize [1939205616#u32,641788683#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,2134309165#u32]
def a3 : State := Array.make 16#usize [1939205616#u32,641788683#u32,1281268521#u32,0#u32,0#u32,0#u32,0#u32,0#u32,141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,2134309165#u32]
def a4 : State := Array.make 16#usize [1939205616#u32,641788683#u32,1281268521#u32,866499727#u32,0#u32,0#u32,0#u32,0#u32,141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,2134309165#u32]
def a5 : State := Array.make 16#usize [1939205616#u32,641788683#u32,1281268521#u32,866499727#u32,385183050#u32,0#u32,0#u32,0#u32,141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,2134309165#u32]
def a6 : State := Array.make 16#usize [1939205616#u32,641788683#u32,1281268521#u32,866499727#u32,385183050#u32,1408789791#u32,0#u32,0#u32,141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,2134309165#u32]
def a7 : State := Array.make 16#usize [1939205616#u32,641788683#u32,1281268521#u32,866499727#u32,385183050#u32,1408789791#u32,1189739305#u32,0#u32,141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,2134309165#u32]
def a8 : State := Array.make 16#usize [1939205616#u32,641788683#u32,1281268521#u32,866499727#u32,385183050#u32,1408789791#u32,1189739305#u32,569851020#u32,141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,2134309165#u32]
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
  | 0 => PV_RunJoin_ValidatorCell4219.s0
  | 1 => PV_RunJoin_ValidatorCell4219.s3
  | 2 => PV_RunJoin_ValidatorCell4219.s5
  | 3 => PV_RunJoin_ValidatorCell4219.s7
  | 4 => PV_RunJoin_ValidatorCell4219.s9
  | 5 => PV_RunJoin_ValidatorCell4219.s11
  | 6 => PV_RunJoin_ValidatorCell4219.s13
  | 7 => PV_RunJoin_ValidatorCell4219.s15
  | 8 => PV_RunJoin_ValidatorCell4219.s17
  | 9 => PV_RunJoin_ValidatorCell4219.s19
  | 10 => PV_RunJoin_ValidatorCell4219.s21
  | 11 => PV_RunJoin_ValidatorCell4219.s23
  | _ => PV_RunJoin_ValidatorCell4219.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1939205616#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨641788683#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1281268521#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨866499727#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨385183050#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1408789791#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1189739305#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨569851020#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell4219.s2,PV_RunJoin_ValidatorCell4219.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell4219.s4,PV_RunJoin_ValidatorCell4219.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell4219.s6,PV_RunJoin_ValidatorCell4219.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell4219.s8,PV_RunJoin_ValidatorCell4219.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell4219.s10,PV_RunJoin_ValidatorCell4219.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell4219.s12,PV_RunJoin_ValidatorCell4219.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell4219.s14,PV_RunJoin_ValidatorCell4219.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell4219.s16,PV_RunJoin_ValidatorCell4219.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell4219.s18,PV_RunJoin_ValidatorCell4219.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell4219.s20,PV_RunJoin_ValidatorCell4219.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell4219.s22,PV_RunJoin_ValidatorCell4219.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell4219

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell4319
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1133998657#u32,190536997#u32,632216762#u32,2145002820#u32,1218690534#u32,1341831920#u32,1813986794#u32,962659369#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,346725128#u32]
def a1 : State := Array.make 16#usize [1133998657#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,346725128#u32]
def a2 : State := Array.make 16#usize [1133998657#u32,190536997#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,346725128#u32]
def a3 : State := Array.make 16#usize [1133998657#u32,190536997#u32,632216762#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,346725128#u32]
def a4 : State := Array.make 16#usize [1133998657#u32,190536997#u32,632216762#u32,2145002820#u32,0#u32,0#u32,0#u32,0#u32,1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,346725128#u32]
def a5 : State := Array.make 16#usize [1133998657#u32,190536997#u32,632216762#u32,2145002820#u32,1218690534#u32,0#u32,0#u32,0#u32,1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,346725128#u32]
def a6 : State := Array.make 16#usize [1133998657#u32,190536997#u32,632216762#u32,2145002820#u32,1218690534#u32,1341831920#u32,0#u32,0#u32,1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,346725128#u32]
def a7 : State := Array.make 16#usize [1133998657#u32,190536997#u32,632216762#u32,2145002820#u32,1218690534#u32,1341831920#u32,1813986794#u32,0#u32,1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,346725128#u32]
def a8 : State := Array.make 16#usize [1133998657#u32,190536997#u32,632216762#u32,2145002820#u32,1218690534#u32,1341831920#u32,1813986794#u32,962659369#u32,1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,346725128#u32]
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
  | 0 => PV_RunJoin_ValidatorCell4319.s0
  | 1 => PV_RunJoin_ValidatorCell4319.s3
  | 2 => PV_RunJoin_ValidatorCell4319.s5
  | 3 => PV_RunJoin_ValidatorCell4319.s7
  | 4 => PV_RunJoin_ValidatorCell4319.s9
  | 5 => PV_RunJoin_ValidatorCell4319.s11
  | 6 => PV_RunJoin_ValidatorCell4319.s13
  | 7 => PV_RunJoin_ValidatorCell4319.s15
  | 8 => PV_RunJoin_ValidatorCell4319.s17
  | 9 => PV_RunJoin_ValidatorCell4319.s19
  | 10 => PV_RunJoin_ValidatorCell4319.s21
  | 11 => PV_RunJoin_ValidatorCell4319.s23
  | _ => PV_RunJoin_ValidatorCell4319.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1133998657#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨190536997#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨632216762#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2145002820#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1218690534#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1341831920#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1813986794#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨962659369#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell4319.s2,PV_RunJoin_ValidatorCell4319.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell4319.s4,PV_RunJoin_ValidatorCell4319.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell4319.s6,PV_RunJoin_ValidatorCell4319.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell4319.s8,PV_RunJoin_ValidatorCell4319.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell4319.s10,PV_RunJoin_ValidatorCell4319.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell4319.s12,PV_RunJoin_ValidatorCell4319.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell4319.s14,PV_RunJoin_ValidatorCell4319.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell4319.s16,PV_RunJoin_ValidatorCell4319.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell4319.s18,PV_RunJoin_ValidatorCell4319.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell4319.s20,PV_RunJoin_ValidatorCell4319.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell4319.s22,PV_RunJoin_ValidatorCell4319.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell4319

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell4419
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1061398933#u32,509112012#u32,1799578086#u32,482877258#u32,2025164722#u32,672733548#u32,359961336#u32,1470147015#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,973366555#u32]
def a1 : State := Array.make 16#usize [1061398933#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,973366555#u32]
def a2 : State := Array.make 16#usize [1061398933#u32,509112012#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,973366555#u32]
def a3 : State := Array.make 16#usize [1061398933#u32,509112012#u32,1799578086#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,973366555#u32]
def a4 : State := Array.make 16#usize [1061398933#u32,509112012#u32,1799578086#u32,482877258#u32,0#u32,0#u32,0#u32,0#u32,1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,973366555#u32]
def a5 : State := Array.make 16#usize [1061398933#u32,509112012#u32,1799578086#u32,482877258#u32,2025164722#u32,0#u32,0#u32,0#u32,1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,973366555#u32]
def a6 : State := Array.make 16#usize [1061398933#u32,509112012#u32,1799578086#u32,482877258#u32,2025164722#u32,672733548#u32,0#u32,0#u32,1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,973366555#u32]
def a7 : State := Array.make 16#usize [1061398933#u32,509112012#u32,1799578086#u32,482877258#u32,2025164722#u32,672733548#u32,359961336#u32,0#u32,1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,973366555#u32]
def a8 : State := Array.make 16#usize [1061398933#u32,509112012#u32,1799578086#u32,482877258#u32,2025164722#u32,672733548#u32,359961336#u32,1470147015#u32,1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,973366555#u32]
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
  | 0 => PV_RunJoin_ValidatorCell4419.s0
  | 1 => PV_RunJoin_ValidatorCell4419.s3
  | 2 => PV_RunJoin_ValidatorCell4419.s5
  | 3 => PV_RunJoin_ValidatorCell4419.s7
  | 4 => PV_RunJoin_ValidatorCell4419.s9
  | 5 => PV_RunJoin_ValidatorCell4419.s11
  | 6 => PV_RunJoin_ValidatorCell4419.s13
  | 7 => PV_RunJoin_ValidatorCell4419.s15
  | 8 => PV_RunJoin_ValidatorCell4419.s17
  | 9 => PV_RunJoin_ValidatorCell4419.s19
  | 10 => PV_RunJoin_ValidatorCell4419.s21
  | 11 => PV_RunJoin_ValidatorCell4419.s23
  | _ => PV_RunJoin_ValidatorCell4419.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1061398933#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨509112012#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1799578086#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨482877258#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2025164722#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨672733548#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨359961336#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1470147015#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell4419.s2,PV_RunJoin_ValidatorCell4419.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell4419.s4,PV_RunJoin_ValidatorCell4419.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell4419.s6,PV_RunJoin_ValidatorCell4419.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell4419.s8,PV_RunJoin_ValidatorCell4419.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell4419.s10,PV_RunJoin_ValidatorCell4419.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell4419.s12,PV_RunJoin_ValidatorCell4419.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell4419.s14,PV_RunJoin_ValidatorCell4419.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell4419.s16,PV_RunJoin_ValidatorCell4419.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell4419.s18,PV_RunJoin_ValidatorCell4419.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell4419.s20,PV_RunJoin_ValidatorCell4419.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell4419.s22,PV_RunJoin_ValidatorCell4419.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell4419
