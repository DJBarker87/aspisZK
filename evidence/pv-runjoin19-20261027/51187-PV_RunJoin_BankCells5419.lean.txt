import R1Z.PV_RunJoin_BankCertificate19
import R1Z.PV_RunJoin_ValidatorGroup5219
import R1Z.PV_RunJoin_ValidatorGroup5519
import R1Z.PV_RunJoin_ValidatorGroup5819
import R1Z.PV_RunJoin_ValidatorGroup6119
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell5419
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1310587138#u32,1547028228#u32,724201667#u32,460418645#u32,1935078033#u32,56710135#u32,329156384#u32,480377036#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,2054173171#u32]
def a1 : State := Array.make 16#usize [1310587138#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,2054173171#u32]
def a2 : State := Array.make 16#usize [1310587138#u32,1547028228#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,2054173171#u32]
def a3 : State := Array.make 16#usize [1310587138#u32,1547028228#u32,724201667#u32,0#u32,0#u32,0#u32,0#u32,0#u32,260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,2054173171#u32]
def a4 : State := Array.make 16#usize [1310587138#u32,1547028228#u32,724201667#u32,460418645#u32,0#u32,0#u32,0#u32,0#u32,260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,2054173171#u32]
def a5 : State := Array.make 16#usize [1310587138#u32,1547028228#u32,724201667#u32,460418645#u32,1935078033#u32,0#u32,0#u32,0#u32,260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,2054173171#u32]
def a6 : State := Array.make 16#usize [1310587138#u32,1547028228#u32,724201667#u32,460418645#u32,1935078033#u32,56710135#u32,0#u32,0#u32,260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,2054173171#u32]
def a7 : State := Array.make 16#usize [1310587138#u32,1547028228#u32,724201667#u32,460418645#u32,1935078033#u32,56710135#u32,329156384#u32,0#u32,260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,2054173171#u32]
def a8 : State := Array.make 16#usize [1310587138#u32,1547028228#u32,724201667#u32,460418645#u32,1935078033#u32,56710135#u32,329156384#u32,480377036#u32,260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,2054173171#u32]
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
  | 0 => PV_RunJoin_ValidatorCell5419.s0
  | 1 => PV_RunJoin_ValidatorCell5419.s3
  | 2 => PV_RunJoin_ValidatorCell5419.s5
  | 3 => PV_RunJoin_ValidatorCell5419.s7
  | 4 => PV_RunJoin_ValidatorCell5419.s9
  | 5 => PV_RunJoin_ValidatorCell5419.s11
  | 6 => PV_RunJoin_ValidatorCell5419.s13
  | 7 => PV_RunJoin_ValidatorCell5419.s15
  | 8 => PV_RunJoin_ValidatorCell5419.s17
  | 9 => PV_RunJoin_ValidatorCell5419.s19
  | 10 => PV_RunJoin_ValidatorCell5419.s21
  | 11 => PV_RunJoin_ValidatorCell5419.s23
  | _ => PV_RunJoin_ValidatorCell5419.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1310587138#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1547028228#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨724201667#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨460418645#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1935078033#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨56710135#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨329156384#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨480377036#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell5419.s2,PV_RunJoin_ValidatorCell5419.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell5419.s4,PV_RunJoin_ValidatorCell5419.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell5419.s6,PV_RunJoin_ValidatorCell5419.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell5419.s8,PV_RunJoin_ValidatorCell5419.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell5419.s10,PV_RunJoin_ValidatorCell5419.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell5419.s12,PV_RunJoin_ValidatorCell5419.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell5419.s14,PV_RunJoin_ValidatorCell5419.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell5419.s16,PV_RunJoin_ValidatorCell5419.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell5419.s18,PV_RunJoin_ValidatorCell5419.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell5419.s20,PV_RunJoin_ValidatorCell5419.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell5419.s22,PV_RunJoin_ValidatorCell5419.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell5419

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell5519
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [126701447#u32,2048228689#u32,1569040746#u32,816942090#u32,934340682#u32,707737539#u32,1640113194#u32,1531834504#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
def a1 : State := Array.make 16#usize [126701447#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
def a2 : State := Array.make 16#usize [126701447#u32,2048228689#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
def a3 : State := Array.make 16#usize [126701447#u32,2048228689#u32,1569040746#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
def a4 : State := Array.make 16#usize [126701447#u32,2048228689#u32,1569040746#u32,816942090#u32,0#u32,0#u32,0#u32,0#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
def a5 : State := Array.make 16#usize [126701447#u32,2048228689#u32,1569040746#u32,816942090#u32,934340682#u32,0#u32,0#u32,0#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
def a6 : State := Array.make 16#usize [126701447#u32,2048228689#u32,1569040746#u32,816942090#u32,934340682#u32,707737539#u32,0#u32,0#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
def a7 : State := Array.make 16#usize [126701447#u32,2048228689#u32,1569040746#u32,816942090#u32,934340682#u32,707737539#u32,1640113194#u32,0#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
def a8 : State := Array.make 16#usize [126701447#u32,2048228689#u32,1569040746#u32,816942090#u32,934340682#u32,707737539#u32,1640113194#u32,1531834504#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
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
  | 0 => PV_RunJoin_ValidatorCell5519.s0
  | 1 => PV_RunJoin_ValidatorCell5519.s3
  | 2 => PV_RunJoin_ValidatorCell5519.s5
  | 3 => PV_RunJoin_ValidatorCell5519.s7
  | 4 => PV_RunJoin_ValidatorCell5519.s9
  | 5 => PV_RunJoin_ValidatorCell5519.s11
  | 6 => PV_RunJoin_ValidatorCell5519.s13
  | 7 => PV_RunJoin_ValidatorCell5519.s15
  | 8 => PV_RunJoin_ValidatorCell5519.s17
  | 9 => PV_RunJoin_ValidatorCell5519.s19
  | 10 => PV_RunJoin_ValidatorCell5519.s21
  | 11 => PV_RunJoin_ValidatorCell5519.s23
  | _ => PV_RunJoin_ValidatorCell5519.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨126701447#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2048228689#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1569040746#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨816942090#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨934340682#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨707737539#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1640113194#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1531834504#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell5519.s2,PV_RunJoin_ValidatorCell5519.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell5519.s4,PV_RunJoin_ValidatorCell5519.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell5519.s6,PV_RunJoin_ValidatorCell5519.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell5519.s8,PV_RunJoin_ValidatorCell5519.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell5519.s10,PV_RunJoin_ValidatorCell5519.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell5519.s12,PV_RunJoin_ValidatorCell5519.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell5519.s14,PV_RunJoin_ValidatorCell5519.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell5519.s16,PV_RunJoin_ValidatorCell5519.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell5519.s18,PV_RunJoin_ValidatorCell5519.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell5519.s20,PV_RunJoin_ValidatorCell5519.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell5519.s22,PV_RunJoin_ValidatorCell5519.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell5519

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell5619
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [2007593611#u32,263026897#u32,269045574#u32,218491882#u32,465723479#u32,2019127874#u32,1644297524#u32,121114825#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
def a1 : State := Array.make 16#usize [2007593611#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
def a2 : State := Array.make 16#usize [2007593611#u32,263026897#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
def a3 : State := Array.make 16#usize [2007593611#u32,263026897#u32,269045574#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
def a4 : State := Array.make 16#usize [2007593611#u32,263026897#u32,269045574#u32,218491882#u32,0#u32,0#u32,0#u32,0#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
def a5 : State := Array.make 16#usize [2007593611#u32,263026897#u32,269045574#u32,218491882#u32,465723479#u32,0#u32,0#u32,0#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
def a6 : State := Array.make 16#usize [2007593611#u32,263026897#u32,269045574#u32,218491882#u32,465723479#u32,2019127874#u32,0#u32,0#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
def a7 : State := Array.make 16#usize [2007593611#u32,263026897#u32,269045574#u32,218491882#u32,465723479#u32,2019127874#u32,1644297524#u32,0#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
def a8 : State := Array.make 16#usize [2007593611#u32,263026897#u32,269045574#u32,218491882#u32,465723479#u32,2019127874#u32,1644297524#u32,121114825#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
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
  | 0 => PV_RunJoin_ValidatorCell5619.s0
  | 1 => PV_RunJoin_ValidatorCell5619.s3
  | 2 => PV_RunJoin_ValidatorCell5619.s5
  | 3 => PV_RunJoin_ValidatorCell5619.s7
  | 4 => PV_RunJoin_ValidatorCell5619.s9
  | 5 => PV_RunJoin_ValidatorCell5619.s11
  | 6 => PV_RunJoin_ValidatorCell5619.s13
  | 7 => PV_RunJoin_ValidatorCell5619.s15
  | 8 => PV_RunJoin_ValidatorCell5619.s17
  | 9 => PV_RunJoin_ValidatorCell5619.s19
  | 10 => PV_RunJoin_ValidatorCell5619.s21
  | 11 => PV_RunJoin_ValidatorCell5619.s23
  | _ => PV_RunJoin_ValidatorCell5619.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨2007593611#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨263026897#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨269045574#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨218491882#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨465723479#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2019127874#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1644297524#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨121114825#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell5619.s2,PV_RunJoin_ValidatorCell5619.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell5619.s4,PV_RunJoin_ValidatorCell5619.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell5619.s6,PV_RunJoin_ValidatorCell5619.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell5619.s8,PV_RunJoin_ValidatorCell5619.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell5619.s10,PV_RunJoin_ValidatorCell5619.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell5619.s12,PV_RunJoin_ValidatorCell5619.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell5619.s14,PV_RunJoin_ValidatorCell5619.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell5619.s16,PV_RunJoin_ValidatorCell5619.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell5619.s18,PV_RunJoin_ValidatorCell5619.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell5619.s20,PV_RunJoin_ValidatorCell5619.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell5619.s22,PV_RunJoin_ValidatorCell5619.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell5619

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell5719
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [659928130#u32,1737073822#u32,588385416#u32,571209364#u32,294479194#u32,1572976171#u32,358772057#u32,1351134296#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
def a1 : State := Array.make 16#usize [659928130#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
def a2 : State := Array.make 16#usize [659928130#u32,1737073822#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
def a3 : State := Array.make 16#usize [659928130#u32,1737073822#u32,588385416#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
def a4 : State := Array.make 16#usize [659928130#u32,1737073822#u32,588385416#u32,571209364#u32,0#u32,0#u32,0#u32,0#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
def a5 : State := Array.make 16#usize [659928130#u32,1737073822#u32,588385416#u32,571209364#u32,294479194#u32,0#u32,0#u32,0#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
def a6 : State := Array.make 16#usize [659928130#u32,1737073822#u32,588385416#u32,571209364#u32,294479194#u32,1572976171#u32,0#u32,0#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
def a7 : State := Array.make 16#usize [659928130#u32,1737073822#u32,588385416#u32,571209364#u32,294479194#u32,1572976171#u32,358772057#u32,0#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
def a8 : State := Array.make 16#usize [659928130#u32,1737073822#u32,588385416#u32,571209364#u32,294479194#u32,1572976171#u32,358772057#u32,1351134296#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
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
  | 0 => PV_RunJoin_ValidatorCell5719.s0
  | 1 => PV_RunJoin_ValidatorCell5719.s3
  | 2 => PV_RunJoin_ValidatorCell5719.s5
  | 3 => PV_RunJoin_ValidatorCell5719.s7
  | 4 => PV_RunJoin_ValidatorCell5719.s9
  | 5 => PV_RunJoin_ValidatorCell5719.s11
  | 6 => PV_RunJoin_ValidatorCell5719.s13
  | 7 => PV_RunJoin_ValidatorCell5719.s15
  | 8 => PV_RunJoin_ValidatorCell5719.s17
  | 9 => PV_RunJoin_ValidatorCell5719.s19
  | 10 => PV_RunJoin_ValidatorCell5719.s21
  | 11 => PV_RunJoin_ValidatorCell5719.s23
  | _ => PV_RunJoin_ValidatorCell5719.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨659928130#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1737073822#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨588385416#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨571209364#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨294479194#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1572976171#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨358772057#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1351134296#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell5719.s2,PV_RunJoin_ValidatorCell5719.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell5719.s4,PV_RunJoin_ValidatorCell5719.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell5719.s6,PV_RunJoin_ValidatorCell5719.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell5719.s8,PV_RunJoin_ValidatorCell5719.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell5719.s10,PV_RunJoin_ValidatorCell5719.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell5719.s12,PV_RunJoin_ValidatorCell5719.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell5719.s14,PV_RunJoin_ValidatorCell5719.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell5719.s16,PV_RunJoin_ValidatorCell5719.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell5719.s18,PV_RunJoin_ValidatorCell5719.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell5719.s20,PV_RunJoin_ValidatorCell5719.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell5719.s22,PV_RunJoin_ValidatorCell5719.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell5719

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell5819
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [295651292#u32,1528951695#u32,967845926#u32,1002855730#u32,1691775382#u32,1825776613#u32,369526834#u32,1655898863#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,248459395#u32]
def a1 : State := Array.make 16#usize [295651292#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,248459395#u32]
def a2 : State := Array.make 16#usize [295651292#u32,1528951695#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,248459395#u32]
def a3 : State := Array.make 16#usize [295651292#u32,1528951695#u32,967845926#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,248459395#u32]
def a4 : State := Array.make 16#usize [295651292#u32,1528951695#u32,967845926#u32,1002855730#u32,0#u32,0#u32,0#u32,0#u32,1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,248459395#u32]
def a5 : State := Array.make 16#usize [295651292#u32,1528951695#u32,967845926#u32,1002855730#u32,1691775382#u32,0#u32,0#u32,0#u32,1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,248459395#u32]
def a6 : State := Array.make 16#usize [295651292#u32,1528951695#u32,967845926#u32,1002855730#u32,1691775382#u32,1825776613#u32,0#u32,0#u32,1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,248459395#u32]
def a7 : State := Array.make 16#usize [295651292#u32,1528951695#u32,967845926#u32,1002855730#u32,1691775382#u32,1825776613#u32,369526834#u32,0#u32,1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,248459395#u32]
def a8 : State := Array.make 16#usize [295651292#u32,1528951695#u32,967845926#u32,1002855730#u32,1691775382#u32,1825776613#u32,369526834#u32,1655898863#u32,1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,248459395#u32]
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
  | 0 => PV_RunJoin_ValidatorCell5819.s0
  | 1 => PV_RunJoin_ValidatorCell5819.s3
  | 2 => PV_RunJoin_ValidatorCell5819.s5
  | 3 => PV_RunJoin_ValidatorCell5819.s7
  | 4 => PV_RunJoin_ValidatorCell5819.s9
  | 5 => PV_RunJoin_ValidatorCell5819.s11
  | 6 => PV_RunJoin_ValidatorCell5819.s13
  | 7 => PV_RunJoin_ValidatorCell5819.s15
  | 8 => PV_RunJoin_ValidatorCell5819.s17
  | 9 => PV_RunJoin_ValidatorCell5819.s19
  | 10 => PV_RunJoin_ValidatorCell5819.s21
  | 11 => PV_RunJoin_ValidatorCell5819.s23
  | _ => PV_RunJoin_ValidatorCell5819.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨295651292#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1528951695#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨967845926#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1002855730#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1691775382#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1825776613#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨369526834#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1655898863#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell5819.s2,PV_RunJoin_ValidatorCell5819.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell5819.s4,PV_RunJoin_ValidatorCell5819.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell5819.s6,PV_RunJoin_ValidatorCell5819.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell5819.s8,PV_RunJoin_ValidatorCell5819.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell5819.s10,PV_RunJoin_ValidatorCell5819.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell5819.s12,PV_RunJoin_ValidatorCell5819.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell5819.s14,PV_RunJoin_ValidatorCell5819.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell5819.s16,PV_RunJoin_ValidatorCell5819.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell5819.s18,PV_RunJoin_ValidatorCell5819.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell5819.s20,PV_RunJoin_ValidatorCell5819.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell5819.s22,PV_RunJoin_ValidatorCell5819.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell5819

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell5919
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1660714618#u32,58624303#u32,617770228#u32,599383446#u32,771361068#u32,1834589194#u32,51322319#u32,276611708#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,1546489432#u32]
def a1 : State := Array.make 16#usize [1660714618#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,1546489432#u32]
def a2 : State := Array.make 16#usize [1660714618#u32,58624303#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,1546489432#u32]
def a3 : State := Array.make 16#usize [1660714618#u32,58624303#u32,617770228#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,1546489432#u32]
def a4 : State := Array.make 16#usize [1660714618#u32,58624303#u32,617770228#u32,599383446#u32,0#u32,0#u32,0#u32,0#u32,1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,1546489432#u32]
def a5 : State := Array.make 16#usize [1660714618#u32,58624303#u32,617770228#u32,599383446#u32,771361068#u32,0#u32,0#u32,0#u32,1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,1546489432#u32]
def a6 : State := Array.make 16#usize [1660714618#u32,58624303#u32,617770228#u32,599383446#u32,771361068#u32,1834589194#u32,0#u32,0#u32,1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,1546489432#u32]
def a7 : State := Array.make 16#usize [1660714618#u32,58624303#u32,617770228#u32,599383446#u32,771361068#u32,1834589194#u32,51322319#u32,0#u32,1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,1546489432#u32]
def a8 : State := Array.make 16#usize [1660714618#u32,58624303#u32,617770228#u32,599383446#u32,771361068#u32,1834589194#u32,51322319#u32,276611708#u32,1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,1546489432#u32]
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
  | 0 => PV_RunJoin_ValidatorCell5919.s0
  | 1 => PV_RunJoin_ValidatorCell5919.s3
  | 2 => PV_RunJoin_ValidatorCell5919.s5
  | 3 => PV_RunJoin_ValidatorCell5919.s7
  | 4 => PV_RunJoin_ValidatorCell5919.s9
  | 5 => PV_RunJoin_ValidatorCell5919.s11
  | 6 => PV_RunJoin_ValidatorCell5919.s13
  | 7 => PV_RunJoin_ValidatorCell5919.s15
  | 8 => PV_RunJoin_ValidatorCell5919.s17
  | 9 => PV_RunJoin_ValidatorCell5919.s19
  | 10 => PV_RunJoin_ValidatorCell5919.s21
  | 11 => PV_RunJoin_ValidatorCell5919.s23
  | _ => PV_RunJoin_ValidatorCell5919.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1660714618#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨58624303#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨617770228#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨599383446#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨771361068#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1834589194#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨51322319#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨276611708#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell5919.s2,PV_RunJoin_ValidatorCell5919.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell5919.s4,PV_RunJoin_ValidatorCell5919.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell5919.s6,PV_RunJoin_ValidatorCell5919.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell5919.s8,PV_RunJoin_ValidatorCell5919.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell5919.s10,PV_RunJoin_ValidatorCell5919.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell5919.s12,PV_RunJoin_ValidatorCell5919.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell5919.s14,PV_RunJoin_ValidatorCell5919.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell5919.s16,PV_RunJoin_ValidatorCell5919.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell5919.s18,PV_RunJoin_ValidatorCell5919.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell5919.s20,PV_RunJoin_ValidatorCell5919.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell5919.s22,PV_RunJoin_ValidatorCell5919.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell5919

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell6019
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1186265903#u32,415151008#u32,1902434632#u32,1450931092#u32,922955725#u32,1977809658#u32,160284130#u32,1987330095#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,1761530072#u32]
def a1 : State := Array.make 16#usize [1186265903#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,1761530072#u32]
def a2 : State := Array.make 16#usize [1186265903#u32,415151008#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,1761530072#u32]
def a3 : State := Array.make 16#usize [1186265903#u32,415151008#u32,1902434632#u32,0#u32,0#u32,0#u32,0#u32,0#u32,19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,1761530072#u32]
def a4 : State := Array.make 16#usize [1186265903#u32,415151008#u32,1902434632#u32,1450931092#u32,0#u32,0#u32,0#u32,0#u32,19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,1761530072#u32]
def a5 : State := Array.make 16#usize [1186265903#u32,415151008#u32,1902434632#u32,1450931092#u32,922955725#u32,0#u32,0#u32,0#u32,19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,1761530072#u32]
def a6 : State := Array.make 16#usize [1186265903#u32,415151008#u32,1902434632#u32,1450931092#u32,922955725#u32,1977809658#u32,0#u32,0#u32,19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,1761530072#u32]
def a7 : State := Array.make 16#usize [1186265903#u32,415151008#u32,1902434632#u32,1450931092#u32,922955725#u32,1977809658#u32,160284130#u32,0#u32,19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,1761530072#u32]
def a8 : State := Array.make 16#usize [1186265903#u32,415151008#u32,1902434632#u32,1450931092#u32,922955725#u32,1977809658#u32,160284130#u32,1987330095#u32,19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,1761530072#u32]
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
  | 0 => PV_RunJoin_ValidatorCell6019.s0
  | 1 => PV_RunJoin_ValidatorCell6019.s3
  | 2 => PV_RunJoin_ValidatorCell6019.s5
  | 3 => PV_RunJoin_ValidatorCell6019.s7
  | 4 => PV_RunJoin_ValidatorCell6019.s9
  | 5 => PV_RunJoin_ValidatorCell6019.s11
  | 6 => PV_RunJoin_ValidatorCell6019.s13
  | 7 => PV_RunJoin_ValidatorCell6019.s15
  | 8 => PV_RunJoin_ValidatorCell6019.s17
  | 9 => PV_RunJoin_ValidatorCell6019.s19
  | 10 => PV_RunJoin_ValidatorCell6019.s21
  | 11 => PV_RunJoin_ValidatorCell6019.s23
  | _ => PV_RunJoin_ValidatorCell6019.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1186265903#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨415151008#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1902434632#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1450931092#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨922955725#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1977809658#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨160284130#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1987330095#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell6019.s2,PV_RunJoin_ValidatorCell6019.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell6019.s4,PV_RunJoin_ValidatorCell6019.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell6019.s6,PV_RunJoin_ValidatorCell6019.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell6019.s8,PV_RunJoin_ValidatorCell6019.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell6019.s10,PV_RunJoin_ValidatorCell6019.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell6019.s12,PV_RunJoin_ValidatorCell6019.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell6019.s14,PV_RunJoin_ValidatorCell6019.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell6019.s16,PV_RunJoin_ValidatorCell6019.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell6019.s18,PV_RunJoin_ValidatorCell6019.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell6019.s20,PV_RunJoin_ValidatorCell6019.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell6019.s22,PV_RunJoin_ValidatorCell6019.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell6019

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell6119
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1635444076#u32,565453809#u32,2007649881#u32,905247732#u32,1187015924#u32,827186728#u32,137720039#u32,588419202#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,103505714#u32]
def a1 : State := Array.make 16#usize [1635444076#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,103505714#u32]
def a2 : State := Array.make 16#usize [1635444076#u32,565453809#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,103505714#u32]
def a3 : State := Array.make 16#usize [1635444076#u32,565453809#u32,2007649881#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,103505714#u32]
def a4 : State := Array.make 16#usize [1635444076#u32,565453809#u32,2007649881#u32,905247732#u32,0#u32,0#u32,0#u32,0#u32,1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,103505714#u32]
def a5 : State := Array.make 16#usize [1635444076#u32,565453809#u32,2007649881#u32,905247732#u32,1187015924#u32,0#u32,0#u32,0#u32,1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,103505714#u32]
def a6 : State := Array.make 16#usize [1635444076#u32,565453809#u32,2007649881#u32,905247732#u32,1187015924#u32,827186728#u32,0#u32,0#u32,1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,103505714#u32]
def a7 : State := Array.make 16#usize [1635444076#u32,565453809#u32,2007649881#u32,905247732#u32,1187015924#u32,827186728#u32,137720039#u32,0#u32,1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,103505714#u32]
def a8 : State := Array.make 16#usize [1635444076#u32,565453809#u32,2007649881#u32,905247732#u32,1187015924#u32,827186728#u32,137720039#u32,588419202#u32,1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,103505714#u32]
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
  | 0 => PV_RunJoin_ValidatorCell6119.s0
  | 1 => PV_RunJoin_ValidatorCell6119.s3
  | 2 => PV_RunJoin_ValidatorCell6119.s5
  | 3 => PV_RunJoin_ValidatorCell6119.s7
  | 4 => PV_RunJoin_ValidatorCell6119.s9
  | 5 => PV_RunJoin_ValidatorCell6119.s11
  | 6 => PV_RunJoin_ValidatorCell6119.s13
  | 7 => PV_RunJoin_ValidatorCell6119.s15
  | 8 => PV_RunJoin_ValidatorCell6119.s17
  | 9 => PV_RunJoin_ValidatorCell6119.s19
  | 10 => PV_RunJoin_ValidatorCell6119.s21
  | 11 => PV_RunJoin_ValidatorCell6119.s23
  | _ => PV_RunJoin_ValidatorCell6119.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1635444076#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨565453809#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2007649881#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨905247732#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1187015924#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨827186728#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨137720039#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨588419202#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell6119.s2,PV_RunJoin_ValidatorCell6119.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell6119.s4,PV_RunJoin_ValidatorCell6119.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell6119.s6,PV_RunJoin_ValidatorCell6119.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell6119.s8,PV_RunJoin_ValidatorCell6119.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell6119.s10,PV_RunJoin_ValidatorCell6119.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell6119.s12,PV_RunJoin_ValidatorCell6119.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell6119.s14,PV_RunJoin_ValidatorCell6119.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell6119.s16,PV_RunJoin_ValidatorCell6119.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell6119.s18,PV_RunJoin_ValidatorCell6119.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell6119.s20,PV_RunJoin_ValidatorCell6119.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell6119.s22,PV_RunJoin_ValidatorCell6119.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell6119

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell6219
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [609870583#u32,958510084#u32,2094278047#u32,743619649#u32,1992887085#u32,2048705761#u32,118223484#u32,1828066596#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,2134309165#u32]
def a1 : State := Array.make 16#usize [609870583#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,2134309165#u32]
def a2 : State := Array.make 16#usize [609870583#u32,958510084#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,2134309165#u32]
def a3 : State := Array.make 16#usize [609870583#u32,958510084#u32,2094278047#u32,0#u32,0#u32,0#u32,0#u32,0#u32,141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,2134309165#u32]
def a4 : State := Array.make 16#usize [609870583#u32,958510084#u32,2094278047#u32,743619649#u32,0#u32,0#u32,0#u32,0#u32,141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,2134309165#u32]
def a5 : State := Array.make 16#usize [609870583#u32,958510084#u32,2094278047#u32,743619649#u32,1992887085#u32,0#u32,0#u32,0#u32,141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,2134309165#u32]
def a6 : State := Array.make 16#usize [609870583#u32,958510084#u32,2094278047#u32,743619649#u32,1992887085#u32,2048705761#u32,0#u32,0#u32,141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,2134309165#u32]
def a7 : State := Array.make 16#usize [609870583#u32,958510084#u32,2094278047#u32,743619649#u32,1992887085#u32,2048705761#u32,118223484#u32,0#u32,141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,2134309165#u32]
def a8 : State := Array.make 16#usize [609870583#u32,958510084#u32,2094278047#u32,743619649#u32,1992887085#u32,2048705761#u32,118223484#u32,1828066596#u32,141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,2134309165#u32]
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
  | 0 => PV_RunJoin_ValidatorCell6219.s0
  | 1 => PV_RunJoin_ValidatorCell6219.s3
  | 2 => PV_RunJoin_ValidatorCell6219.s5
  | 3 => PV_RunJoin_ValidatorCell6219.s7
  | 4 => PV_RunJoin_ValidatorCell6219.s9
  | 5 => PV_RunJoin_ValidatorCell6219.s11
  | 6 => PV_RunJoin_ValidatorCell6219.s13
  | 7 => PV_RunJoin_ValidatorCell6219.s15
  | 8 => PV_RunJoin_ValidatorCell6219.s17
  | 9 => PV_RunJoin_ValidatorCell6219.s19
  | 10 => PV_RunJoin_ValidatorCell6219.s21
  | 11 => PV_RunJoin_ValidatorCell6219.s23
  | _ => PV_RunJoin_ValidatorCell6219.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨609870583#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨958510084#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2094278047#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨743619649#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1992887085#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2048705761#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨118223484#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1828066596#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell6219.s2,PV_RunJoin_ValidatorCell6219.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell6219.s4,PV_RunJoin_ValidatorCell6219.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell6219.s6,PV_RunJoin_ValidatorCell6219.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell6219.s8,PV_RunJoin_ValidatorCell6219.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell6219.s10,PV_RunJoin_ValidatorCell6219.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell6219.s12,PV_RunJoin_ValidatorCell6219.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell6219.s14,PV_RunJoin_ValidatorCell6219.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell6219.s16,PV_RunJoin_ValidatorCell6219.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell6219.s18,PV_RunJoin_ValidatorCell6219.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell6219.s20,PV_RunJoin_ValidatorCell6219.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell6219.s22,PV_RunJoin_ValidatorCell6219.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell6219
