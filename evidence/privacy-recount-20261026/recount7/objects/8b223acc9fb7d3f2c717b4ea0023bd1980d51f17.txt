import R1Z.PV_RunJoin_BankCertificate19
import R1Z.PV_RunJoin_ValidatorGroup0719
import R1Z.PV_RunJoin_ValidatorGroup1019
import R1Z.PV_RunJoin_ValidatorGroup1319
import R1Z.PV_RunJoin_ValidatorGroup1619
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell0919
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1088882418#u32,1343804471#u32,734616548#u32,13922508#u32,2033036789#u32,781570573#u32,1154493927#u32,1197511955#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2041#u32,2058#u32,2075#u32,2092#u32,2109#u32,2126#u32,2143#u32,1095964789#u32]
def a1 : State := Array.make 16#usize [1088882418#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2041#u32,2058#u32,2075#u32,2092#u32,2109#u32,2126#u32,2143#u32,1095964789#u32]
def a2 : State := Array.make 16#usize [1088882418#u32,1343804471#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2041#u32,2058#u32,2075#u32,2092#u32,2109#u32,2126#u32,2143#u32,1095964789#u32]
def a3 : State := Array.make 16#usize [1088882418#u32,1343804471#u32,734616548#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2041#u32,2058#u32,2075#u32,2092#u32,2109#u32,2126#u32,2143#u32,1095964789#u32]
def a4 : State := Array.make 16#usize [1088882418#u32,1343804471#u32,734616548#u32,13922508#u32,0#u32,0#u32,0#u32,0#u32,2041#u32,2058#u32,2075#u32,2092#u32,2109#u32,2126#u32,2143#u32,1095964789#u32]
def a5 : State := Array.make 16#usize [1088882418#u32,1343804471#u32,734616548#u32,13922508#u32,2033036789#u32,0#u32,0#u32,0#u32,2041#u32,2058#u32,2075#u32,2092#u32,2109#u32,2126#u32,2143#u32,1095964789#u32]
def a6 : State := Array.make 16#usize [1088882418#u32,1343804471#u32,734616548#u32,13922508#u32,2033036789#u32,781570573#u32,0#u32,0#u32,2041#u32,2058#u32,2075#u32,2092#u32,2109#u32,2126#u32,2143#u32,1095964789#u32]
def a7 : State := Array.make 16#usize [1088882418#u32,1343804471#u32,734616548#u32,13922508#u32,2033036789#u32,781570573#u32,1154493927#u32,0#u32,2041#u32,2058#u32,2075#u32,2092#u32,2109#u32,2126#u32,2143#u32,1095964789#u32]
def a8 : State := Array.make 16#usize [1088882418#u32,1343804471#u32,734616548#u32,13922508#u32,2033036789#u32,781570573#u32,1154493927#u32,1197511955#u32,2041#u32,2058#u32,2075#u32,2092#u32,2109#u32,2126#u32,2143#u32,1095964789#u32]
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
  | 0 => PV_RunJoin_ValidatorCell0919.s0
  | 1 => PV_RunJoin_ValidatorCell0919.s3
  | 2 => PV_RunJoin_ValidatorCell0919.s5
  | 3 => PV_RunJoin_ValidatorCell0919.s7
  | 4 => PV_RunJoin_ValidatorCell0919.s9
  | 5 => PV_RunJoin_ValidatorCell0919.s11
  | 6 => PV_RunJoin_ValidatorCell0919.s13
  | 7 => PV_RunJoin_ValidatorCell0919.s15
  | 8 => PV_RunJoin_ValidatorCell0919.s17
  | 9 => PV_RunJoin_ValidatorCell0919.s19
  | 10 => PV_RunJoin_ValidatorCell0919.s21
  | 11 => PV_RunJoin_ValidatorCell0919.s23
  | _ => PV_RunJoin_ValidatorCell0919.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1088882418#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1343804471#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨734616548#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨13922508#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2033036789#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨781570573#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1154493927#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1197511955#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell0919.s2,PV_RunJoin_ValidatorCell0919.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell0919.s4,PV_RunJoin_ValidatorCell0919.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell0919.s6,PV_RunJoin_ValidatorCell0919.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell0919.s8,PV_RunJoin_ValidatorCell0919.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell0919.s10,PV_RunJoin_ValidatorCell0919.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell0919.s12,PV_RunJoin_ValidatorCell0919.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell0919.s14,PV_RunJoin_ValidatorCell0919.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell0919.s16,PV_RunJoin_ValidatorCell0919.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell0919.s18,PV_RunJoin_ValidatorCell0919.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell0919.s20,PV_RunJoin_ValidatorCell0919.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell0919.s22,PV_RunJoin_ValidatorCell0919.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell0919

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell1019
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [600625215#u32,237354909#u32,439972622#u32,263907834#u32,1075778621#u32,569932161#u32,1744169643#u32,1373371366#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2061#u32,2078#u32,2095#u32,2112#u32,2129#u32,2146#u32,2163#u32,1095964809#u32]
def a1 : State := Array.make 16#usize [600625215#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2061#u32,2078#u32,2095#u32,2112#u32,2129#u32,2146#u32,2163#u32,1095964809#u32]
def a2 : State := Array.make 16#usize [600625215#u32,237354909#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2061#u32,2078#u32,2095#u32,2112#u32,2129#u32,2146#u32,2163#u32,1095964809#u32]
def a3 : State := Array.make 16#usize [600625215#u32,237354909#u32,439972622#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2061#u32,2078#u32,2095#u32,2112#u32,2129#u32,2146#u32,2163#u32,1095964809#u32]
def a4 : State := Array.make 16#usize [600625215#u32,237354909#u32,439972622#u32,263907834#u32,0#u32,0#u32,0#u32,0#u32,2061#u32,2078#u32,2095#u32,2112#u32,2129#u32,2146#u32,2163#u32,1095964809#u32]
def a5 : State := Array.make 16#usize [600625215#u32,237354909#u32,439972622#u32,263907834#u32,1075778621#u32,0#u32,0#u32,0#u32,2061#u32,2078#u32,2095#u32,2112#u32,2129#u32,2146#u32,2163#u32,1095964809#u32]
def a6 : State := Array.make 16#usize [600625215#u32,237354909#u32,439972622#u32,263907834#u32,1075778621#u32,569932161#u32,0#u32,0#u32,2061#u32,2078#u32,2095#u32,2112#u32,2129#u32,2146#u32,2163#u32,1095964809#u32]
def a7 : State := Array.make 16#usize [600625215#u32,237354909#u32,439972622#u32,263907834#u32,1075778621#u32,569932161#u32,1744169643#u32,0#u32,2061#u32,2078#u32,2095#u32,2112#u32,2129#u32,2146#u32,2163#u32,1095964809#u32]
def a8 : State := Array.make 16#usize [600625215#u32,237354909#u32,439972622#u32,263907834#u32,1075778621#u32,569932161#u32,1744169643#u32,1373371366#u32,2061#u32,2078#u32,2095#u32,2112#u32,2129#u32,2146#u32,2163#u32,1095964809#u32]
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
  | 0 => PV_RunJoin_ValidatorCell1019.s0
  | 1 => PV_RunJoin_ValidatorCell1019.s3
  | 2 => PV_RunJoin_ValidatorCell1019.s5
  | 3 => PV_RunJoin_ValidatorCell1019.s7
  | 4 => PV_RunJoin_ValidatorCell1019.s9
  | 5 => PV_RunJoin_ValidatorCell1019.s11
  | 6 => PV_RunJoin_ValidatorCell1019.s13
  | 7 => PV_RunJoin_ValidatorCell1019.s15
  | 8 => PV_RunJoin_ValidatorCell1019.s17
  | 9 => PV_RunJoin_ValidatorCell1019.s19
  | 10 => PV_RunJoin_ValidatorCell1019.s21
  | 11 => PV_RunJoin_ValidatorCell1019.s23
  | _ => PV_RunJoin_ValidatorCell1019.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨600625215#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨237354909#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨439972622#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨263907834#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1075778621#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨569932161#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1744169643#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1373371366#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell1019.s2,PV_RunJoin_ValidatorCell1019.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell1019.s4,PV_RunJoin_ValidatorCell1019.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell1019.s6,PV_RunJoin_ValidatorCell1019.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell1019.s8,PV_RunJoin_ValidatorCell1019.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell1019.s10,PV_RunJoin_ValidatorCell1019.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell1019.s12,PV_RunJoin_ValidatorCell1019.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell1019.s14,PV_RunJoin_ValidatorCell1019.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell1019.s16,PV_RunJoin_ValidatorCell1019.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell1019.s18,PV_RunJoin_ValidatorCell1019.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell1019.s20,PV_RunJoin_ValidatorCell1019.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell1019.s22,PV_RunJoin_ValidatorCell1019.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell1019

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell1119
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1180202183#u32,1734852885#u32,1208353062#u32,189889914#u32,943421826#u32,507090805#u32,389529953#u32,896398700#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2081#u32,2098#u32,2115#u32,2132#u32,2149#u32,2166#u32,2183#u32,1095964829#u32]
def a1 : State := Array.make 16#usize [1180202183#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2081#u32,2098#u32,2115#u32,2132#u32,2149#u32,2166#u32,2183#u32,1095964829#u32]
def a2 : State := Array.make 16#usize [1180202183#u32,1734852885#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2081#u32,2098#u32,2115#u32,2132#u32,2149#u32,2166#u32,2183#u32,1095964829#u32]
def a3 : State := Array.make 16#usize [1180202183#u32,1734852885#u32,1208353062#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2081#u32,2098#u32,2115#u32,2132#u32,2149#u32,2166#u32,2183#u32,1095964829#u32]
def a4 : State := Array.make 16#usize [1180202183#u32,1734852885#u32,1208353062#u32,189889914#u32,0#u32,0#u32,0#u32,0#u32,2081#u32,2098#u32,2115#u32,2132#u32,2149#u32,2166#u32,2183#u32,1095964829#u32]
def a5 : State := Array.make 16#usize [1180202183#u32,1734852885#u32,1208353062#u32,189889914#u32,943421826#u32,0#u32,0#u32,0#u32,2081#u32,2098#u32,2115#u32,2132#u32,2149#u32,2166#u32,2183#u32,1095964829#u32]
def a6 : State := Array.make 16#usize [1180202183#u32,1734852885#u32,1208353062#u32,189889914#u32,943421826#u32,507090805#u32,0#u32,0#u32,2081#u32,2098#u32,2115#u32,2132#u32,2149#u32,2166#u32,2183#u32,1095964829#u32]
def a7 : State := Array.make 16#usize [1180202183#u32,1734852885#u32,1208353062#u32,189889914#u32,943421826#u32,507090805#u32,389529953#u32,0#u32,2081#u32,2098#u32,2115#u32,2132#u32,2149#u32,2166#u32,2183#u32,1095964829#u32]
def a8 : State := Array.make 16#usize [1180202183#u32,1734852885#u32,1208353062#u32,189889914#u32,943421826#u32,507090805#u32,389529953#u32,896398700#u32,2081#u32,2098#u32,2115#u32,2132#u32,2149#u32,2166#u32,2183#u32,1095964829#u32]
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
  | 0 => PV_RunJoin_ValidatorCell1119.s0
  | 1 => PV_RunJoin_ValidatorCell1119.s3
  | 2 => PV_RunJoin_ValidatorCell1119.s5
  | 3 => PV_RunJoin_ValidatorCell1119.s7
  | 4 => PV_RunJoin_ValidatorCell1119.s9
  | 5 => PV_RunJoin_ValidatorCell1119.s11
  | 6 => PV_RunJoin_ValidatorCell1119.s13
  | 7 => PV_RunJoin_ValidatorCell1119.s15
  | 8 => PV_RunJoin_ValidatorCell1119.s17
  | 9 => PV_RunJoin_ValidatorCell1119.s19
  | 10 => PV_RunJoin_ValidatorCell1119.s21
  | 11 => PV_RunJoin_ValidatorCell1119.s23
  | _ => PV_RunJoin_ValidatorCell1119.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1180202183#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1734852885#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1208353062#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨189889914#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨943421826#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨507090805#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨389529953#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨896398700#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell1119.s2,PV_RunJoin_ValidatorCell1119.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell1119.s4,PV_RunJoin_ValidatorCell1119.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell1119.s6,PV_RunJoin_ValidatorCell1119.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell1119.s8,PV_RunJoin_ValidatorCell1119.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell1119.s10,PV_RunJoin_ValidatorCell1119.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell1119.s12,PV_RunJoin_ValidatorCell1119.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell1119.s14,PV_RunJoin_ValidatorCell1119.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell1119.s16,PV_RunJoin_ValidatorCell1119.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell1119.s18,PV_RunJoin_ValidatorCell1119.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell1119.s20,PV_RunJoin_ValidatorCell1119.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell1119.s22,PV_RunJoin_ValidatorCell1119.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell1119

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell1219
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [2101#u32,2118#u32,2135#u32,2152#u32,2169#u32,2186#u32,2203#u32,2220#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,439700881#u32,730194574#u32,1601626633#u32,1478607356#u32,953523754#u32,1749099081#u32,333248178#u32,711569769#u32]
def a1 : State := Array.make 16#usize [2101#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,439700881#u32,730194574#u32,1601626633#u32,1478607356#u32,953523754#u32,1749099081#u32,333248178#u32,711569769#u32]
def a2 : State := Array.make 16#usize [2101#u32,2118#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,439700881#u32,730194574#u32,1601626633#u32,1478607356#u32,953523754#u32,1749099081#u32,333248178#u32,711569769#u32]
def a3 : State := Array.make 16#usize [2101#u32,2118#u32,2135#u32,0#u32,0#u32,0#u32,0#u32,0#u32,439700881#u32,730194574#u32,1601626633#u32,1478607356#u32,953523754#u32,1749099081#u32,333248178#u32,711569769#u32]
def a4 : State := Array.make 16#usize [2101#u32,2118#u32,2135#u32,2152#u32,0#u32,0#u32,0#u32,0#u32,439700881#u32,730194574#u32,1601626633#u32,1478607356#u32,953523754#u32,1749099081#u32,333248178#u32,711569769#u32]
def a5 : State := Array.make 16#usize [2101#u32,2118#u32,2135#u32,2152#u32,2169#u32,0#u32,0#u32,0#u32,439700881#u32,730194574#u32,1601626633#u32,1478607356#u32,953523754#u32,1749099081#u32,333248178#u32,711569769#u32]
def a6 : State := Array.make 16#usize [2101#u32,2118#u32,2135#u32,2152#u32,2169#u32,2186#u32,0#u32,0#u32,439700881#u32,730194574#u32,1601626633#u32,1478607356#u32,953523754#u32,1749099081#u32,333248178#u32,711569769#u32]
def a7 : State := Array.make 16#usize [2101#u32,2118#u32,2135#u32,2152#u32,2169#u32,2186#u32,2203#u32,0#u32,439700881#u32,730194574#u32,1601626633#u32,1478607356#u32,953523754#u32,1749099081#u32,333248178#u32,711569769#u32]
def a8 : State := Array.make 16#usize [2101#u32,2118#u32,2135#u32,2152#u32,2169#u32,2186#u32,2203#u32,2220#u32,439700881#u32,730194574#u32,1601626633#u32,1478607356#u32,953523754#u32,1749099081#u32,333248178#u32,711569769#u32]
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
  | 0 => PV_RunJoin_ValidatorCell1219.s0
  | 1 => PV_RunJoin_ValidatorCell1219.s3
  | 2 => PV_RunJoin_ValidatorCell1219.s5
  | 3 => PV_RunJoin_ValidatorCell1219.s7
  | 4 => PV_RunJoin_ValidatorCell1219.s9
  | 5 => PV_RunJoin_ValidatorCell1219.s11
  | 6 => PV_RunJoin_ValidatorCell1219.s13
  | 7 => PV_RunJoin_ValidatorCell1219.s15
  | 8 => PV_RunJoin_ValidatorCell1219.s17
  | 9 => PV_RunJoin_ValidatorCell1219.s19
  | 10 => PV_RunJoin_ValidatorCell1219.s21
  | 11 => PV_RunJoin_ValidatorCell1219.s23
  | _ => PV_RunJoin_ValidatorCell1219.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨2101#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2118#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2135#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2152#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2169#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2186#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2203#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2220#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell1219.s2,PV_RunJoin_ValidatorCell1219.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell1219.s4,PV_RunJoin_ValidatorCell1219.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell1219.s6,PV_RunJoin_ValidatorCell1219.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell1219.s8,PV_RunJoin_ValidatorCell1219.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell1219.s10,PV_RunJoin_ValidatorCell1219.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell1219.s12,PV_RunJoin_ValidatorCell1219.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell1219.s14,PV_RunJoin_ValidatorCell1219.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell1219.s16,PV_RunJoin_ValidatorCell1219.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell1219.s18,PV_RunJoin_ValidatorCell1219.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell1219.s20,PV_RunJoin_ValidatorCell1219.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell1219.s22,PV_RunJoin_ValidatorCell1219.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell1219

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell1319
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [891777458#u32,519287294#u32,1981395871#u32,1193798350#u32,1897410699#u32,1175699129#u32,1224545956#u32,757035799#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2121#u32,2138#u32,2155#u32,2172#u32,2189#u32,2206#u32,2223#u32,1095964869#u32]
def a1 : State := Array.make 16#usize [891777458#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2121#u32,2138#u32,2155#u32,2172#u32,2189#u32,2206#u32,2223#u32,1095964869#u32]
def a2 : State := Array.make 16#usize [891777458#u32,519287294#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2121#u32,2138#u32,2155#u32,2172#u32,2189#u32,2206#u32,2223#u32,1095964869#u32]
def a3 : State := Array.make 16#usize [891777458#u32,519287294#u32,1981395871#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2121#u32,2138#u32,2155#u32,2172#u32,2189#u32,2206#u32,2223#u32,1095964869#u32]
def a4 : State := Array.make 16#usize [891777458#u32,519287294#u32,1981395871#u32,1193798350#u32,0#u32,0#u32,0#u32,0#u32,2121#u32,2138#u32,2155#u32,2172#u32,2189#u32,2206#u32,2223#u32,1095964869#u32]
def a5 : State := Array.make 16#usize [891777458#u32,519287294#u32,1981395871#u32,1193798350#u32,1897410699#u32,0#u32,0#u32,0#u32,2121#u32,2138#u32,2155#u32,2172#u32,2189#u32,2206#u32,2223#u32,1095964869#u32]
def a6 : State := Array.make 16#usize [891777458#u32,519287294#u32,1981395871#u32,1193798350#u32,1897410699#u32,1175699129#u32,0#u32,0#u32,2121#u32,2138#u32,2155#u32,2172#u32,2189#u32,2206#u32,2223#u32,1095964869#u32]
def a7 : State := Array.make 16#usize [891777458#u32,519287294#u32,1981395871#u32,1193798350#u32,1897410699#u32,1175699129#u32,1224545956#u32,0#u32,2121#u32,2138#u32,2155#u32,2172#u32,2189#u32,2206#u32,2223#u32,1095964869#u32]
def a8 : State := Array.make 16#usize [891777458#u32,519287294#u32,1981395871#u32,1193798350#u32,1897410699#u32,1175699129#u32,1224545956#u32,757035799#u32,2121#u32,2138#u32,2155#u32,2172#u32,2189#u32,2206#u32,2223#u32,1095964869#u32]
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
  | 0 => PV_RunJoin_ValidatorCell1319.s0
  | 1 => PV_RunJoin_ValidatorCell1319.s3
  | 2 => PV_RunJoin_ValidatorCell1319.s5
  | 3 => PV_RunJoin_ValidatorCell1319.s7
  | 4 => PV_RunJoin_ValidatorCell1319.s9
  | 5 => PV_RunJoin_ValidatorCell1319.s11
  | 6 => PV_RunJoin_ValidatorCell1319.s13
  | 7 => PV_RunJoin_ValidatorCell1319.s15
  | 8 => PV_RunJoin_ValidatorCell1319.s17
  | 9 => PV_RunJoin_ValidatorCell1319.s19
  | 10 => PV_RunJoin_ValidatorCell1319.s21
  | 11 => PV_RunJoin_ValidatorCell1319.s23
  | _ => PV_RunJoin_ValidatorCell1319.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨891777458#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨519287294#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1981395871#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1193798350#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1897410699#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1175699129#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1224545956#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨757035799#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell1319.s2,PV_RunJoin_ValidatorCell1319.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell1319.s4,PV_RunJoin_ValidatorCell1319.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell1319.s6,PV_RunJoin_ValidatorCell1319.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell1319.s8,PV_RunJoin_ValidatorCell1319.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell1319.s10,PV_RunJoin_ValidatorCell1319.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell1319.s12,PV_RunJoin_ValidatorCell1319.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell1319.s14,PV_RunJoin_ValidatorCell1319.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell1319.s16,PV_RunJoin_ValidatorCell1319.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell1319.s18,PV_RunJoin_ValidatorCell1319.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell1319.s20,PV_RunJoin_ValidatorCell1319.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell1319.s22,PV_RunJoin_ValidatorCell1319.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell1319

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell1419
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1134127212#u32,1758195919#u32,1492236623#u32,1856566444#u32,896074385#u32,533821444#u32,2118230281#u32,1863638021#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2141#u32,2158#u32,2175#u32,2192#u32,2209#u32,2226#u32,2243#u32,1095964889#u32]
def a1 : State := Array.make 16#usize [1134127212#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2141#u32,2158#u32,2175#u32,2192#u32,2209#u32,2226#u32,2243#u32,1095964889#u32]
def a2 : State := Array.make 16#usize [1134127212#u32,1758195919#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2141#u32,2158#u32,2175#u32,2192#u32,2209#u32,2226#u32,2243#u32,1095964889#u32]
def a3 : State := Array.make 16#usize [1134127212#u32,1758195919#u32,1492236623#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2141#u32,2158#u32,2175#u32,2192#u32,2209#u32,2226#u32,2243#u32,1095964889#u32]
def a4 : State := Array.make 16#usize [1134127212#u32,1758195919#u32,1492236623#u32,1856566444#u32,0#u32,0#u32,0#u32,0#u32,2141#u32,2158#u32,2175#u32,2192#u32,2209#u32,2226#u32,2243#u32,1095964889#u32]
def a5 : State := Array.make 16#usize [1134127212#u32,1758195919#u32,1492236623#u32,1856566444#u32,896074385#u32,0#u32,0#u32,0#u32,2141#u32,2158#u32,2175#u32,2192#u32,2209#u32,2226#u32,2243#u32,1095964889#u32]
def a6 : State := Array.make 16#usize [1134127212#u32,1758195919#u32,1492236623#u32,1856566444#u32,896074385#u32,533821444#u32,0#u32,0#u32,2141#u32,2158#u32,2175#u32,2192#u32,2209#u32,2226#u32,2243#u32,1095964889#u32]
def a7 : State := Array.make 16#usize [1134127212#u32,1758195919#u32,1492236623#u32,1856566444#u32,896074385#u32,533821444#u32,2118230281#u32,0#u32,2141#u32,2158#u32,2175#u32,2192#u32,2209#u32,2226#u32,2243#u32,1095964889#u32]
def a8 : State := Array.make 16#usize [1134127212#u32,1758195919#u32,1492236623#u32,1856566444#u32,896074385#u32,533821444#u32,2118230281#u32,1863638021#u32,2141#u32,2158#u32,2175#u32,2192#u32,2209#u32,2226#u32,2243#u32,1095964889#u32]
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
  | 0 => PV_RunJoin_ValidatorCell1419.s0
  | 1 => PV_RunJoin_ValidatorCell1419.s3
  | 2 => PV_RunJoin_ValidatorCell1419.s5
  | 3 => PV_RunJoin_ValidatorCell1419.s7
  | 4 => PV_RunJoin_ValidatorCell1419.s9
  | 5 => PV_RunJoin_ValidatorCell1419.s11
  | 6 => PV_RunJoin_ValidatorCell1419.s13
  | 7 => PV_RunJoin_ValidatorCell1419.s15
  | 8 => PV_RunJoin_ValidatorCell1419.s17
  | 9 => PV_RunJoin_ValidatorCell1419.s19
  | 10 => PV_RunJoin_ValidatorCell1419.s21
  | 11 => PV_RunJoin_ValidatorCell1419.s23
  | _ => PV_RunJoin_ValidatorCell1419.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1134127212#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1758195919#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1492236623#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1856566444#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨896074385#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨533821444#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2118230281#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1863638021#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell1419.s2,PV_RunJoin_ValidatorCell1419.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell1419.s4,PV_RunJoin_ValidatorCell1419.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell1419.s6,PV_RunJoin_ValidatorCell1419.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell1419.s8,PV_RunJoin_ValidatorCell1419.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell1419.s10,PV_RunJoin_ValidatorCell1419.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell1419.s12,PV_RunJoin_ValidatorCell1419.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell1419.s14,PV_RunJoin_ValidatorCell1419.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell1419.s16,PV_RunJoin_ValidatorCell1419.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell1419.s18,PV_RunJoin_ValidatorCell1419.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell1419.s20,PV_RunJoin_ValidatorCell1419.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell1419.s22,PV_RunJoin_ValidatorCell1419.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell1419

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell1519
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [2161#u32,2178#u32,2195#u32,2212#u32,2229#u32,2246#u32,2263#u32,2280#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,785640667#u32,939877614#u32,365887579#u32,1554146132#u32,884924304#u32,1762346545#u32,308452542#u32,1713942709#u32]
def a1 : State := Array.make 16#usize [2161#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,785640667#u32,939877614#u32,365887579#u32,1554146132#u32,884924304#u32,1762346545#u32,308452542#u32,1713942709#u32]
def a2 : State := Array.make 16#usize [2161#u32,2178#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,785640667#u32,939877614#u32,365887579#u32,1554146132#u32,884924304#u32,1762346545#u32,308452542#u32,1713942709#u32]
def a3 : State := Array.make 16#usize [2161#u32,2178#u32,2195#u32,0#u32,0#u32,0#u32,0#u32,0#u32,785640667#u32,939877614#u32,365887579#u32,1554146132#u32,884924304#u32,1762346545#u32,308452542#u32,1713942709#u32]
def a4 : State := Array.make 16#usize [2161#u32,2178#u32,2195#u32,2212#u32,0#u32,0#u32,0#u32,0#u32,785640667#u32,939877614#u32,365887579#u32,1554146132#u32,884924304#u32,1762346545#u32,308452542#u32,1713942709#u32]
def a5 : State := Array.make 16#usize [2161#u32,2178#u32,2195#u32,2212#u32,2229#u32,0#u32,0#u32,0#u32,785640667#u32,939877614#u32,365887579#u32,1554146132#u32,884924304#u32,1762346545#u32,308452542#u32,1713942709#u32]
def a6 : State := Array.make 16#usize [2161#u32,2178#u32,2195#u32,2212#u32,2229#u32,2246#u32,0#u32,0#u32,785640667#u32,939877614#u32,365887579#u32,1554146132#u32,884924304#u32,1762346545#u32,308452542#u32,1713942709#u32]
def a7 : State := Array.make 16#usize [2161#u32,2178#u32,2195#u32,2212#u32,2229#u32,2246#u32,2263#u32,0#u32,785640667#u32,939877614#u32,365887579#u32,1554146132#u32,884924304#u32,1762346545#u32,308452542#u32,1713942709#u32]
def a8 : State := Array.make 16#usize [2161#u32,2178#u32,2195#u32,2212#u32,2229#u32,2246#u32,2263#u32,2280#u32,785640667#u32,939877614#u32,365887579#u32,1554146132#u32,884924304#u32,1762346545#u32,308452542#u32,1713942709#u32]
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
  | 0 => PV_RunJoin_ValidatorCell1519.s0
  | 1 => PV_RunJoin_ValidatorCell1519.s3
  | 2 => PV_RunJoin_ValidatorCell1519.s5
  | 3 => PV_RunJoin_ValidatorCell1519.s7
  | 4 => PV_RunJoin_ValidatorCell1519.s9
  | 5 => PV_RunJoin_ValidatorCell1519.s11
  | 6 => PV_RunJoin_ValidatorCell1519.s13
  | 7 => PV_RunJoin_ValidatorCell1519.s15
  | 8 => PV_RunJoin_ValidatorCell1519.s17
  | 9 => PV_RunJoin_ValidatorCell1519.s19
  | 10 => PV_RunJoin_ValidatorCell1519.s21
  | 11 => PV_RunJoin_ValidatorCell1519.s23
  | _ => PV_RunJoin_ValidatorCell1519.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨2161#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2178#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2195#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2212#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2229#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2246#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2263#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2280#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell1519.s2,PV_RunJoin_ValidatorCell1519.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell1519.s4,PV_RunJoin_ValidatorCell1519.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell1519.s6,PV_RunJoin_ValidatorCell1519.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell1519.s8,PV_RunJoin_ValidatorCell1519.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell1519.s10,PV_RunJoin_ValidatorCell1519.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell1519.s12,PV_RunJoin_ValidatorCell1519.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell1519.s14,PV_RunJoin_ValidatorCell1519.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell1519.s16,PV_RunJoin_ValidatorCell1519.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell1519.s18,PV_RunJoin_ValidatorCell1519.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell1519.s20,PV_RunJoin_ValidatorCell1519.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell1519.s22,PV_RunJoin_ValidatorCell1519.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell1519

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell1619
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [2181#u32,2198#u32,2215#u32,2232#u32,2249#u32,2266#u32,2283#u32,2300#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1563279367#u32,1990384079#u32,1317503545#u32,1053962530#u32,1761249440#u32,14780773#u32,549276084#u32,562712644#u32]
def a1 : State := Array.make 16#usize [2181#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1563279367#u32,1990384079#u32,1317503545#u32,1053962530#u32,1761249440#u32,14780773#u32,549276084#u32,562712644#u32]
def a2 : State := Array.make 16#usize [2181#u32,2198#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1563279367#u32,1990384079#u32,1317503545#u32,1053962530#u32,1761249440#u32,14780773#u32,549276084#u32,562712644#u32]
def a3 : State := Array.make 16#usize [2181#u32,2198#u32,2215#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1563279367#u32,1990384079#u32,1317503545#u32,1053962530#u32,1761249440#u32,14780773#u32,549276084#u32,562712644#u32]
def a4 : State := Array.make 16#usize [2181#u32,2198#u32,2215#u32,2232#u32,0#u32,0#u32,0#u32,0#u32,1563279367#u32,1990384079#u32,1317503545#u32,1053962530#u32,1761249440#u32,14780773#u32,549276084#u32,562712644#u32]
def a5 : State := Array.make 16#usize [2181#u32,2198#u32,2215#u32,2232#u32,2249#u32,0#u32,0#u32,0#u32,1563279367#u32,1990384079#u32,1317503545#u32,1053962530#u32,1761249440#u32,14780773#u32,549276084#u32,562712644#u32]
def a6 : State := Array.make 16#usize [2181#u32,2198#u32,2215#u32,2232#u32,2249#u32,2266#u32,0#u32,0#u32,1563279367#u32,1990384079#u32,1317503545#u32,1053962530#u32,1761249440#u32,14780773#u32,549276084#u32,562712644#u32]
def a7 : State := Array.make 16#usize [2181#u32,2198#u32,2215#u32,2232#u32,2249#u32,2266#u32,2283#u32,0#u32,1563279367#u32,1990384079#u32,1317503545#u32,1053962530#u32,1761249440#u32,14780773#u32,549276084#u32,562712644#u32]
def a8 : State := Array.make 16#usize [2181#u32,2198#u32,2215#u32,2232#u32,2249#u32,2266#u32,2283#u32,2300#u32,1563279367#u32,1990384079#u32,1317503545#u32,1053962530#u32,1761249440#u32,14780773#u32,549276084#u32,562712644#u32]
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
  | 0 => PV_RunJoin_ValidatorCell1619.s0
  | 1 => PV_RunJoin_ValidatorCell1619.s3
  | 2 => PV_RunJoin_ValidatorCell1619.s5
  | 3 => PV_RunJoin_ValidatorCell1619.s7
  | 4 => PV_RunJoin_ValidatorCell1619.s9
  | 5 => PV_RunJoin_ValidatorCell1619.s11
  | 6 => PV_RunJoin_ValidatorCell1619.s13
  | 7 => PV_RunJoin_ValidatorCell1619.s15
  | 8 => PV_RunJoin_ValidatorCell1619.s17
  | 9 => PV_RunJoin_ValidatorCell1619.s19
  | 10 => PV_RunJoin_ValidatorCell1619.s21
  | 11 => PV_RunJoin_ValidatorCell1619.s23
  | _ => PV_RunJoin_ValidatorCell1619.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨2181#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2198#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2215#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2232#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2249#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2266#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2283#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2300#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell1619.s2,PV_RunJoin_ValidatorCell1619.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell1619.s4,PV_RunJoin_ValidatorCell1619.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell1619.s6,PV_RunJoin_ValidatorCell1619.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell1619.s8,PV_RunJoin_ValidatorCell1619.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell1619.s10,PV_RunJoin_ValidatorCell1619.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell1619.s12,PV_RunJoin_ValidatorCell1619.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell1619.s14,PV_RunJoin_ValidatorCell1619.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell1619.s16,PV_RunJoin_ValidatorCell1619.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell1619.s18,PV_RunJoin_ValidatorCell1619.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell1619.s20,PV_RunJoin_ValidatorCell1619.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell1619.s22,PV_RunJoin_ValidatorCell1619.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell1619

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell1719
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [620824211#u32,300099494#u32,1668011682#u32,374649414#u32,1359169338#u32,1742041081#u32,1575185854#u32,1782871725#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2201#u32,2218#u32,2235#u32,2252#u32,2269#u32,2286#u32,2303#u32,1095964949#u32]
def a1 : State := Array.make 16#usize [620824211#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2201#u32,2218#u32,2235#u32,2252#u32,2269#u32,2286#u32,2303#u32,1095964949#u32]
def a2 : State := Array.make 16#usize [620824211#u32,300099494#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2201#u32,2218#u32,2235#u32,2252#u32,2269#u32,2286#u32,2303#u32,1095964949#u32]
def a3 : State := Array.make 16#usize [620824211#u32,300099494#u32,1668011682#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2201#u32,2218#u32,2235#u32,2252#u32,2269#u32,2286#u32,2303#u32,1095964949#u32]
def a4 : State := Array.make 16#usize [620824211#u32,300099494#u32,1668011682#u32,374649414#u32,0#u32,0#u32,0#u32,0#u32,2201#u32,2218#u32,2235#u32,2252#u32,2269#u32,2286#u32,2303#u32,1095964949#u32]
def a5 : State := Array.make 16#usize [620824211#u32,300099494#u32,1668011682#u32,374649414#u32,1359169338#u32,0#u32,0#u32,0#u32,2201#u32,2218#u32,2235#u32,2252#u32,2269#u32,2286#u32,2303#u32,1095964949#u32]
def a6 : State := Array.make 16#usize [620824211#u32,300099494#u32,1668011682#u32,374649414#u32,1359169338#u32,1742041081#u32,0#u32,0#u32,2201#u32,2218#u32,2235#u32,2252#u32,2269#u32,2286#u32,2303#u32,1095964949#u32]
def a7 : State := Array.make 16#usize [620824211#u32,300099494#u32,1668011682#u32,374649414#u32,1359169338#u32,1742041081#u32,1575185854#u32,0#u32,2201#u32,2218#u32,2235#u32,2252#u32,2269#u32,2286#u32,2303#u32,1095964949#u32]
def a8 : State := Array.make 16#usize [620824211#u32,300099494#u32,1668011682#u32,374649414#u32,1359169338#u32,1742041081#u32,1575185854#u32,1782871725#u32,2201#u32,2218#u32,2235#u32,2252#u32,2269#u32,2286#u32,2303#u32,1095964949#u32]
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
  | 0 => PV_RunJoin_ValidatorCell1719.s0
  | 1 => PV_RunJoin_ValidatorCell1719.s3
  | 2 => PV_RunJoin_ValidatorCell1719.s5
  | 3 => PV_RunJoin_ValidatorCell1719.s7
  | 4 => PV_RunJoin_ValidatorCell1719.s9
  | 5 => PV_RunJoin_ValidatorCell1719.s11
  | 6 => PV_RunJoin_ValidatorCell1719.s13
  | 7 => PV_RunJoin_ValidatorCell1719.s15
  | 8 => PV_RunJoin_ValidatorCell1719.s17
  | 9 => PV_RunJoin_ValidatorCell1719.s19
  | 10 => PV_RunJoin_ValidatorCell1719.s21
  | 11 => PV_RunJoin_ValidatorCell1719.s23
  | _ => PV_RunJoin_ValidatorCell1719.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨620824211#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨300099494#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1668011682#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨374649414#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1359169338#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1742041081#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1575185854#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1782871725#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell1719.s2,PV_RunJoin_ValidatorCell1719.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell1719.s4,PV_RunJoin_ValidatorCell1719.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell1719.s6,PV_RunJoin_ValidatorCell1719.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell1719.s8,PV_RunJoin_ValidatorCell1719.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell1719.s10,PV_RunJoin_ValidatorCell1719.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell1719.s12,PV_RunJoin_ValidatorCell1719.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell1719.s14,PV_RunJoin_ValidatorCell1719.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell1719.s16,PV_RunJoin_ValidatorCell1719.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell1719.s18,PV_RunJoin_ValidatorCell1719.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell1719.s20,PV_RunJoin_ValidatorCell1719.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell1719.s22,PV_RunJoin_ValidatorCell1719.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell1719
