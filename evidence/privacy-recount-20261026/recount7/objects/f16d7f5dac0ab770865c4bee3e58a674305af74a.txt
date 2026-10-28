import R1Z.PV_RunJoin_BankCertificate19
import R1Z.PV_RunJoin_ValidatorGroup6119
import R1Z.PV_RunJoin_ValidatorGroup6419
import R1Z.PV_RunJoin_ValidatorGroup6719
import R1Z.PV_RunJoin_ValidatorGroup7019
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell6319
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1640108137#u32,330515254#u32,212366917#u32,1785570475#u32,1241175939#u32,132178283#u32,1767391975#u32,136033189#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,346725128#u32]
def a1 : State := Array.make 16#usize [1640108137#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,346725128#u32]
def a2 : State := Array.make 16#usize [1640108137#u32,330515254#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,346725128#u32]
def a3 : State := Array.make 16#usize [1640108137#u32,330515254#u32,212366917#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,346725128#u32]
def a4 : State := Array.make 16#usize [1640108137#u32,330515254#u32,212366917#u32,1785570475#u32,0#u32,0#u32,0#u32,0#u32,1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,346725128#u32]
def a5 : State := Array.make 16#usize [1640108137#u32,330515254#u32,212366917#u32,1785570475#u32,1241175939#u32,0#u32,0#u32,0#u32,1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,346725128#u32]
def a6 : State := Array.make 16#usize [1640108137#u32,330515254#u32,212366917#u32,1785570475#u32,1241175939#u32,132178283#u32,0#u32,0#u32,1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,346725128#u32]
def a7 : State := Array.make 16#usize [1640108137#u32,330515254#u32,212366917#u32,1785570475#u32,1241175939#u32,132178283#u32,1767391975#u32,0#u32,1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,346725128#u32]
def a8 : State := Array.make 16#usize [1640108137#u32,330515254#u32,212366917#u32,1785570475#u32,1241175939#u32,132178283#u32,1767391975#u32,136033189#u32,1119858538#u32,128294437#u32,939091034#u32,659145897#u32,1933666768#u32,903679201#u32,1182639487#u32,346725128#u32]
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
  | 0 => PV_RunJoin_ValidatorCell6319.s0
  | 1 => PV_RunJoin_ValidatorCell6319.s3
  | 2 => PV_RunJoin_ValidatorCell6319.s5
  | 3 => PV_RunJoin_ValidatorCell6319.s7
  | 4 => PV_RunJoin_ValidatorCell6319.s9
  | 5 => PV_RunJoin_ValidatorCell6319.s11
  | 6 => PV_RunJoin_ValidatorCell6319.s13
  | 7 => PV_RunJoin_ValidatorCell6319.s15
  | 8 => PV_RunJoin_ValidatorCell6319.s17
  | 9 => PV_RunJoin_ValidatorCell6319.s19
  | 10 => PV_RunJoin_ValidatorCell6319.s21
  | 11 => PV_RunJoin_ValidatorCell6319.s23
  | _ => PV_RunJoin_ValidatorCell6319.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1640108137#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨330515254#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨212366917#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1785570475#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1241175939#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨132178283#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1767391975#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨136033189#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell6319.s2,PV_RunJoin_ValidatorCell6319.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell6319.s4,PV_RunJoin_ValidatorCell6319.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell6319.s6,PV_RunJoin_ValidatorCell6319.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell6319.s8,PV_RunJoin_ValidatorCell6319.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell6319.s10,PV_RunJoin_ValidatorCell6319.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell6319.s12,PV_RunJoin_ValidatorCell6319.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell6319.s14,PV_RunJoin_ValidatorCell6319.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell6319.s16,PV_RunJoin_ValidatorCell6319.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell6319.s18,PV_RunJoin_ValidatorCell6319.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell6319.s20,PV_RunJoin_ValidatorCell6319.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell6319.s22,PV_RunJoin_ValidatorCell6319.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell6319

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell6419
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [432585881#u32,1344347431#u32,436199667#u32,1321219941#u32,1344313237#u32,719981873#u32,669780265#u32,1723074008#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,973366555#u32]
def a1 : State := Array.make 16#usize [432585881#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,973366555#u32]
def a2 : State := Array.make 16#usize [432585881#u32,1344347431#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,973366555#u32]
def a3 : State := Array.make 16#usize [432585881#u32,1344347431#u32,436199667#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,973366555#u32]
def a4 : State := Array.make 16#usize [432585881#u32,1344347431#u32,436199667#u32,1321219941#u32,0#u32,0#u32,0#u32,0#u32,1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,973366555#u32]
def a5 : State := Array.make 16#usize [432585881#u32,1344347431#u32,436199667#u32,1321219941#u32,1344313237#u32,0#u32,0#u32,0#u32,1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,973366555#u32]
def a6 : State := Array.make 16#usize [432585881#u32,1344347431#u32,436199667#u32,1321219941#u32,1344313237#u32,719981873#u32,0#u32,0#u32,1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,973366555#u32]
def a7 : State := Array.make 16#usize [432585881#u32,1344347431#u32,436199667#u32,1321219941#u32,1344313237#u32,719981873#u32,669780265#u32,0#u32,1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,973366555#u32]
def a8 : State := Array.make 16#usize [432585881#u32,1344347431#u32,436199667#u32,1321219941#u32,1344313237#u32,719981873#u32,669780265#u32,1723074008#u32,1057897051#u32,1132946363#u32,794377079#u32,1971564389#u32,1255722275#u32,926653737#u32,2031728153#u32,973366555#u32]
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
  | 0 => PV_RunJoin_ValidatorCell6419.s0
  | 1 => PV_RunJoin_ValidatorCell6419.s3
  | 2 => PV_RunJoin_ValidatorCell6419.s5
  | 3 => PV_RunJoin_ValidatorCell6419.s7
  | 4 => PV_RunJoin_ValidatorCell6419.s9
  | 5 => PV_RunJoin_ValidatorCell6419.s11
  | 6 => PV_RunJoin_ValidatorCell6419.s13
  | 7 => PV_RunJoin_ValidatorCell6419.s15
  | 8 => PV_RunJoin_ValidatorCell6419.s17
  | 9 => PV_RunJoin_ValidatorCell6419.s19
  | 10 => PV_RunJoin_ValidatorCell6419.s21
  | 11 => PV_RunJoin_ValidatorCell6419.s23
  | _ => PV_RunJoin_ValidatorCell6419.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨432585881#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1344347431#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨436199667#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1321219941#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1344313237#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨719981873#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨669780265#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1723074008#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell6419.s2,PV_RunJoin_ValidatorCell6419.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell6419.s4,PV_RunJoin_ValidatorCell6419.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell6419.s6,PV_RunJoin_ValidatorCell6419.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell6419.s8,PV_RunJoin_ValidatorCell6419.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell6419.s10,PV_RunJoin_ValidatorCell6419.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell6419.s12,PV_RunJoin_ValidatorCell6419.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell6419.s14,PV_RunJoin_ValidatorCell6419.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell6419.s16,PV_RunJoin_ValidatorCell6419.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell6419.s18,PV_RunJoin_ValidatorCell6419.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell6419.s20,PV_RunJoin_ValidatorCell6419.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell6419.s22,PV_RunJoin_ValidatorCell6419.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell6419

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell6519
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1134116828#u32,504509963#u32,1796983347#u32,1413555044#u32,1091344596#u32,1299793962#u32,1007871819#u32,653735563#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,803983598#u32]
def a1 : State := Array.make 16#usize [1134116828#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,803983598#u32]
def a2 : State := Array.make 16#usize [1134116828#u32,504509963#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,803983598#u32]
def a3 : State := Array.make 16#usize [1134116828#u32,504509963#u32,1796983347#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,803983598#u32]
def a4 : State := Array.make 16#usize [1134116828#u32,504509963#u32,1796983347#u32,1413555044#u32,0#u32,0#u32,0#u32,0#u32,1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,803983598#u32]
def a5 : State := Array.make 16#usize [1134116828#u32,504509963#u32,1796983347#u32,1413555044#u32,1091344596#u32,0#u32,0#u32,0#u32,1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,803983598#u32]
def a6 : State := Array.make 16#usize [1134116828#u32,504509963#u32,1796983347#u32,1413555044#u32,1091344596#u32,1299793962#u32,0#u32,0#u32,1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,803983598#u32]
def a7 : State := Array.make 16#usize [1134116828#u32,504509963#u32,1796983347#u32,1413555044#u32,1091344596#u32,1299793962#u32,1007871819#u32,0#u32,1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,803983598#u32]
def a8 : State := Array.make 16#usize [1134116828#u32,504509963#u32,1796983347#u32,1413555044#u32,1091344596#u32,1299793962#u32,1007871819#u32,653735563#u32,1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,803983598#u32]
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
  | 0 => PV_RunJoin_ValidatorCell6519.s0
  | 1 => PV_RunJoin_ValidatorCell6519.s3
  | 2 => PV_RunJoin_ValidatorCell6519.s5
  | 3 => PV_RunJoin_ValidatorCell6519.s7
  | 4 => PV_RunJoin_ValidatorCell6519.s9
  | 5 => PV_RunJoin_ValidatorCell6519.s11
  | 6 => PV_RunJoin_ValidatorCell6519.s13
  | 7 => PV_RunJoin_ValidatorCell6519.s15
  | 8 => PV_RunJoin_ValidatorCell6519.s17
  | 9 => PV_RunJoin_ValidatorCell6519.s19
  | 10 => PV_RunJoin_ValidatorCell6519.s21
  | 11 => PV_RunJoin_ValidatorCell6519.s23
  | _ => PV_RunJoin_ValidatorCell6519.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1134116828#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨504509963#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1796983347#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1413555044#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1091344596#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1299793962#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1007871819#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨653735563#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell6519.s2,PV_RunJoin_ValidatorCell6519.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell6519.s4,PV_RunJoin_ValidatorCell6519.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell6519.s6,PV_RunJoin_ValidatorCell6519.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell6519.s8,PV_RunJoin_ValidatorCell6519.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell6519.s10,PV_RunJoin_ValidatorCell6519.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell6519.s12,PV_RunJoin_ValidatorCell6519.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell6519.s14,PV_RunJoin_ValidatorCell6519.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell6519.s16,PV_RunJoin_ValidatorCell6519.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell6519.s18,PV_RunJoin_ValidatorCell6519.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell6519.s20,PV_RunJoin_ValidatorCell6519.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell6519.s22,PV_RunJoin_ValidatorCell6519.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell6519

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell6619
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [779295644#u32,1030234634#u32,105546947#u32,1848021183#u32,1259417564#u32,1402874809#u32,1412830686#u32,1654786357#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,1657047221#u32]
def a1 : State := Array.make 16#usize [779295644#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,1657047221#u32]
def a2 : State := Array.make 16#usize [779295644#u32,1030234634#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,1657047221#u32]
def a3 : State := Array.make 16#usize [779295644#u32,1030234634#u32,105546947#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,1657047221#u32]
def a4 : State := Array.make 16#usize [779295644#u32,1030234634#u32,105546947#u32,1848021183#u32,0#u32,0#u32,0#u32,0#u32,1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,1657047221#u32]
def a5 : State := Array.make 16#usize [779295644#u32,1030234634#u32,105546947#u32,1848021183#u32,1259417564#u32,0#u32,0#u32,0#u32,1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,1657047221#u32]
def a6 : State := Array.make 16#usize [779295644#u32,1030234634#u32,105546947#u32,1848021183#u32,1259417564#u32,1402874809#u32,0#u32,0#u32,1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,1657047221#u32]
def a7 : State := Array.make 16#usize [779295644#u32,1030234634#u32,105546947#u32,1848021183#u32,1259417564#u32,1402874809#u32,1412830686#u32,0#u32,1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,1657047221#u32]
def a8 : State := Array.make 16#usize [779295644#u32,1030234634#u32,105546947#u32,1848021183#u32,1259417564#u32,1402874809#u32,1412830686#u32,1654786357#u32,1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,1657047221#u32]
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
  | 0 => PV_RunJoin_ValidatorCell6619.s0
  | 1 => PV_RunJoin_ValidatorCell6619.s3
  | 2 => PV_RunJoin_ValidatorCell6619.s5
  | 3 => PV_RunJoin_ValidatorCell6619.s7
  | 4 => PV_RunJoin_ValidatorCell6619.s9
  | 5 => PV_RunJoin_ValidatorCell6619.s11
  | 6 => PV_RunJoin_ValidatorCell6619.s13
  | 7 => PV_RunJoin_ValidatorCell6619.s15
  | 8 => PV_RunJoin_ValidatorCell6619.s17
  | 9 => PV_RunJoin_ValidatorCell6619.s19
  | 10 => PV_RunJoin_ValidatorCell6619.s21
  | 11 => PV_RunJoin_ValidatorCell6619.s23
  | _ => PV_RunJoin_ValidatorCell6619.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨779295644#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1030234634#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨105546947#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1848021183#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1259417564#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1402874809#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1412830686#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1654786357#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell6619.s2,PV_RunJoin_ValidatorCell6619.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell6619.s4,PV_RunJoin_ValidatorCell6619.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell6619.s6,PV_RunJoin_ValidatorCell6619.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell6619.s8,PV_RunJoin_ValidatorCell6619.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell6619.s10,PV_RunJoin_ValidatorCell6619.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell6619.s12,PV_RunJoin_ValidatorCell6619.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell6619.s14,PV_RunJoin_ValidatorCell6619.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell6619.s16,PV_RunJoin_ValidatorCell6619.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell6619.s18,PV_RunJoin_ValidatorCell6619.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell6619.s20,PV_RunJoin_ValidatorCell6619.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell6619.s22,PV_RunJoin_ValidatorCell6619.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell6619

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell6719
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [641432107#u32,640429421#u32,874903178#u32,930860174#u32,778988106#u32,1148923135#u32,1488375597#u32,266199979#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
def a1 : State := Array.make 16#usize [641432107#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
def a2 : State := Array.make 16#usize [641432107#u32,640429421#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
def a3 : State := Array.make 16#usize [641432107#u32,640429421#u32,874903178#u32,0#u32,0#u32,0#u32,0#u32,0#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
def a4 : State := Array.make 16#usize [641432107#u32,640429421#u32,874903178#u32,930860174#u32,0#u32,0#u32,0#u32,0#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
def a5 : State := Array.make 16#usize [641432107#u32,640429421#u32,874903178#u32,930860174#u32,778988106#u32,0#u32,0#u32,0#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
def a6 : State := Array.make 16#usize [641432107#u32,640429421#u32,874903178#u32,930860174#u32,778988106#u32,1148923135#u32,0#u32,0#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
def a7 : State := Array.make 16#usize [641432107#u32,640429421#u32,874903178#u32,930860174#u32,778988106#u32,1148923135#u32,1488375597#u32,0#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
def a8 : State := Array.make 16#usize [641432107#u32,640429421#u32,874903178#u32,930860174#u32,778988106#u32,1148923135#u32,1488375597#u32,266199979#u32,244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,1841894216#u32]
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
  | 0 => PV_RunJoin_ValidatorCell6719.s0
  | 1 => PV_RunJoin_ValidatorCell6719.s3
  | 2 => PV_RunJoin_ValidatorCell6719.s5
  | 3 => PV_RunJoin_ValidatorCell6719.s7
  | 4 => PV_RunJoin_ValidatorCell6719.s9
  | 5 => PV_RunJoin_ValidatorCell6719.s11
  | 6 => PV_RunJoin_ValidatorCell6719.s13
  | 7 => PV_RunJoin_ValidatorCell6719.s15
  | 8 => PV_RunJoin_ValidatorCell6719.s17
  | 9 => PV_RunJoin_ValidatorCell6719.s19
  | 10 => PV_RunJoin_ValidatorCell6719.s21
  | 11 => PV_RunJoin_ValidatorCell6719.s23
  | _ => PV_RunJoin_ValidatorCell6719.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨641432107#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨640429421#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨874903178#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨930860174#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨778988106#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1148923135#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1488375597#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨266199979#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell6719.s2,PV_RunJoin_ValidatorCell6719.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell6719.s4,PV_RunJoin_ValidatorCell6719.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell6719.s6,PV_RunJoin_ValidatorCell6719.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell6719.s8,PV_RunJoin_ValidatorCell6719.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell6719.s10,PV_RunJoin_ValidatorCell6719.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell6719.s12,PV_RunJoin_ValidatorCell6719.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell6719.s14,PV_RunJoin_ValidatorCell6719.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell6719.s16,PV_RunJoin_ValidatorCell6719.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell6719.s18,PV_RunJoin_ValidatorCell6719.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell6719.s20,PV_RunJoin_ValidatorCell6719.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell6719.s22,PV_RunJoin_ValidatorCell6719.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell6719

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell6819
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [719727911#u32,1261141874#u32,1037425088#u32,1528290707#u32,696744339#u32,983928879#u32,1739454800#u32,712455604#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
def a1 : State := Array.make 16#usize [719727911#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
def a2 : State := Array.make 16#usize [719727911#u32,1261141874#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
def a3 : State := Array.make 16#usize [719727911#u32,1261141874#u32,1037425088#u32,0#u32,0#u32,0#u32,0#u32,0#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
def a4 : State := Array.make 16#usize [719727911#u32,1261141874#u32,1037425088#u32,1528290707#u32,0#u32,0#u32,0#u32,0#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
def a5 : State := Array.make 16#usize [719727911#u32,1261141874#u32,1037425088#u32,1528290707#u32,696744339#u32,0#u32,0#u32,0#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
def a6 : State := Array.make 16#usize [719727911#u32,1261141874#u32,1037425088#u32,1528290707#u32,696744339#u32,983928879#u32,0#u32,0#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
def a7 : State := Array.make 16#usize [719727911#u32,1261141874#u32,1037425088#u32,1528290707#u32,696744339#u32,983928879#u32,1739454800#u32,0#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
def a8 : State := Array.make 16#usize [719727911#u32,1261141874#u32,1037425088#u32,1528290707#u32,696744339#u32,983928879#u32,1739454800#u32,712455604#u32,673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,1807663260#u32]
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
  | 0 => PV_RunJoin_ValidatorCell6819.s0
  | 1 => PV_RunJoin_ValidatorCell6819.s3
  | 2 => PV_RunJoin_ValidatorCell6819.s5
  | 3 => PV_RunJoin_ValidatorCell6819.s7
  | 4 => PV_RunJoin_ValidatorCell6819.s9
  | 5 => PV_RunJoin_ValidatorCell6819.s11
  | 6 => PV_RunJoin_ValidatorCell6819.s13
  | 7 => PV_RunJoin_ValidatorCell6819.s15
  | 8 => PV_RunJoin_ValidatorCell6819.s17
  | 9 => PV_RunJoin_ValidatorCell6819.s19
  | 10 => PV_RunJoin_ValidatorCell6819.s21
  | 11 => PV_RunJoin_ValidatorCell6819.s23
  | _ => PV_RunJoin_ValidatorCell6819.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨719727911#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1261141874#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1037425088#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1528290707#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨696744339#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨983928879#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1739454800#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨712455604#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell6819.s2,PV_RunJoin_ValidatorCell6819.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell6819.s4,PV_RunJoin_ValidatorCell6819.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell6819.s6,PV_RunJoin_ValidatorCell6819.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell6819.s8,PV_RunJoin_ValidatorCell6819.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell6819.s10,PV_RunJoin_ValidatorCell6819.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell6819.s12,PV_RunJoin_ValidatorCell6819.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell6819.s14,PV_RunJoin_ValidatorCell6819.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell6819.s16,PV_RunJoin_ValidatorCell6819.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell6819.s18,PV_RunJoin_ValidatorCell6819.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell6819.s20,PV_RunJoin_ValidatorCell6819.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell6819.s22,PV_RunJoin_ValidatorCell6819.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell6819

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell6919
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [844628622#u32,2057670925#u32,2054832692#u32,931597647#u32,1691905484#u32,10140345#u32,2116907504#u32,1823343454#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
def a1 : State := Array.make 16#usize [844628622#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
def a2 : State := Array.make 16#usize [844628622#u32,2057670925#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
def a3 : State := Array.make 16#usize [844628622#u32,2057670925#u32,2054832692#u32,0#u32,0#u32,0#u32,0#u32,0#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
def a4 : State := Array.make 16#usize [844628622#u32,2057670925#u32,2054832692#u32,931597647#u32,0#u32,0#u32,0#u32,0#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
def a5 : State := Array.make 16#usize [844628622#u32,2057670925#u32,2054832692#u32,931597647#u32,1691905484#u32,0#u32,0#u32,0#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
def a6 : State := Array.make 16#usize [844628622#u32,2057670925#u32,2054832692#u32,931597647#u32,1691905484#u32,10140345#u32,0#u32,0#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
def a7 : State := Array.make 16#usize [844628622#u32,2057670925#u32,2054832692#u32,931597647#u32,1691905484#u32,10140345#u32,2116907504#u32,0#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
def a8 : State := Array.make 16#usize [844628622#u32,2057670925#u32,2054832692#u32,931597647#u32,1691905484#u32,10140345#u32,2116907504#u32,1823343454#u32,27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,1649667347#u32]
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
  | 0 => PV_RunJoin_ValidatorCell6919.s0
  | 1 => PV_RunJoin_ValidatorCell6919.s3
  | 2 => PV_RunJoin_ValidatorCell6919.s5
  | 3 => PV_RunJoin_ValidatorCell6919.s7
  | 4 => PV_RunJoin_ValidatorCell6919.s9
  | 5 => PV_RunJoin_ValidatorCell6919.s11
  | 6 => PV_RunJoin_ValidatorCell6919.s13
  | 7 => PV_RunJoin_ValidatorCell6919.s15
  | 8 => PV_RunJoin_ValidatorCell6919.s17
  | 9 => PV_RunJoin_ValidatorCell6919.s19
  | 10 => PV_RunJoin_ValidatorCell6919.s21
  | 11 => PV_RunJoin_ValidatorCell6919.s23
  | _ => PV_RunJoin_ValidatorCell6919.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨844628622#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2057670925#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2054832692#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨931597647#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1691905484#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨10140345#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2116907504#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1823343454#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell6919.s2,PV_RunJoin_ValidatorCell6919.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell6919.s4,PV_RunJoin_ValidatorCell6919.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell6919.s6,PV_RunJoin_ValidatorCell6919.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell6919.s8,PV_RunJoin_ValidatorCell6919.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell6919.s10,PV_RunJoin_ValidatorCell6919.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell6919.s12,PV_RunJoin_ValidatorCell6919.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell6919.s14,PV_RunJoin_ValidatorCell6919.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell6919.s16,PV_RunJoin_ValidatorCell6919.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell6919.s18,PV_RunJoin_ValidatorCell6919.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell6919.s20,PV_RunJoin_ValidatorCell6919.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell6919.s22,PV_RunJoin_ValidatorCell6919.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell6919

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell7019
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [2054510981#u32,1825804774#u32,418288139#u32,378397545#u32,1185114525#u32,81172068#u32,361707637#u32,1111542572#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
def a1 : State := Array.make 16#usize [2054510981#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
def a2 : State := Array.make 16#usize [2054510981#u32,1825804774#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
def a3 : State := Array.make 16#usize [2054510981#u32,1825804774#u32,418288139#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
def a4 : State := Array.make 16#usize [2054510981#u32,1825804774#u32,418288139#u32,378397545#u32,0#u32,0#u32,0#u32,0#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
def a5 : State := Array.make 16#usize [2054510981#u32,1825804774#u32,418288139#u32,378397545#u32,1185114525#u32,0#u32,0#u32,0#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
def a6 : State := Array.make 16#usize [2054510981#u32,1825804774#u32,418288139#u32,378397545#u32,1185114525#u32,81172068#u32,0#u32,0#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
def a7 : State := Array.make 16#usize [2054510981#u32,1825804774#u32,418288139#u32,378397545#u32,1185114525#u32,81172068#u32,361707637#u32,0#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
def a8 : State := Array.make 16#usize [2054510981#u32,1825804774#u32,418288139#u32,378397545#u32,1185114525#u32,81172068#u32,361707637#u32,1111542572#u32,1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,602005867#u32]
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
  | 0 => PV_RunJoin_ValidatorCell7019.s0
  | 1 => PV_RunJoin_ValidatorCell7019.s3
  | 2 => PV_RunJoin_ValidatorCell7019.s5
  | 3 => PV_RunJoin_ValidatorCell7019.s7
  | 4 => PV_RunJoin_ValidatorCell7019.s9
  | 5 => PV_RunJoin_ValidatorCell7019.s11
  | 6 => PV_RunJoin_ValidatorCell7019.s13
  | 7 => PV_RunJoin_ValidatorCell7019.s15
  | 8 => PV_RunJoin_ValidatorCell7019.s17
  | 9 => PV_RunJoin_ValidatorCell7019.s19
  | 10 => PV_RunJoin_ValidatorCell7019.s21
  | 11 => PV_RunJoin_ValidatorCell7019.s23
  | _ => PV_RunJoin_ValidatorCell7019.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨2054510981#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1825804774#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨418288139#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨378397545#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1185114525#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨81172068#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨361707637#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1111542572#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell7019.s2,PV_RunJoin_ValidatorCell7019.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell7019.s4,PV_RunJoin_ValidatorCell7019.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell7019.s6,PV_RunJoin_ValidatorCell7019.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell7019.s8,PV_RunJoin_ValidatorCell7019.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell7019.s10,PV_RunJoin_ValidatorCell7019.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell7019.s12,PV_RunJoin_ValidatorCell7019.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell7019.s14,PV_RunJoin_ValidatorCell7019.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell7019.s16,PV_RunJoin_ValidatorCell7019.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell7019.s18,PV_RunJoin_ValidatorCell7019.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell7019.s20,PV_RunJoin_ValidatorCell7019.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell7019.s22,PV_RunJoin_ValidatorCell7019.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell7019

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell7119
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1107000820#u32,1338554320#u32,488374647#u32,453509918#u32,222991326#u32,1075792838#u32,352883826#u32,459345458#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
def a1 : State := Array.make 16#usize [1107000820#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
def a2 : State := Array.make 16#usize [1107000820#u32,1338554320#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
def a3 : State := Array.make 16#usize [1107000820#u32,1338554320#u32,488374647#u32,0#u32,0#u32,0#u32,0#u32,0#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
def a4 : State := Array.make 16#usize [1107000820#u32,1338554320#u32,488374647#u32,453509918#u32,0#u32,0#u32,0#u32,0#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
def a5 : State := Array.make 16#usize [1107000820#u32,1338554320#u32,488374647#u32,453509918#u32,222991326#u32,0#u32,0#u32,0#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
def a6 : State := Array.make 16#usize [1107000820#u32,1338554320#u32,488374647#u32,453509918#u32,222991326#u32,1075792838#u32,0#u32,0#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
def a7 : State := Array.make 16#usize [1107000820#u32,1338554320#u32,488374647#u32,453509918#u32,222991326#u32,1075792838#u32,352883826#u32,0#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
def a8 : State := Array.make 16#usize [1107000820#u32,1338554320#u32,488374647#u32,453509918#u32,222991326#u32,1075792838#u32,352883826#u32,459345458#u32,418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,749307875#u32]
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
  | 0 => PV_RunJoin_ValidatorCell7119.s0
  | 1 => PV_RunJoin_ValidatorCell7119.s3
  | 2 => PV_RunJoin_ValidatorCell7119.s5
  | 3 => PV_RunJoin_ValidatorCell7119.s7
  | 4 => PV_RunJoin_ValidatorCell7119.s9
  | 5 => PV_RunJoin_ValidatorCell7119.s11
  | 6 => PV_RunJoin_ValidatorCell7119.s13
  | 7 => PV_RunJoin_ValidatorCell7119.s15
  | 8 => PV_RunJoin_ValidatorCell7119.s17
  | 9 => PV_RunJoin_ValidatorCell7119.s19
  | 10 => PV_RunJoin_ValidatorCell7119.s21
  | 11 => PV_RunJoin_ValidatorCell7119.s23
  | _ => PV_RunJoin_ValidatorCell7119.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1107000820#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1338554320#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨488374647#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨453509918#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨222991326#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1075792838#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨352883826#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨459345458#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell7119.s2,PV_RunJoin_ValidatorCell7119.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell7119.s4,PV_RunJoin_ValidatorCell7119.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell7119.s6,PV_RunJoin_ValidatorCell7119.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell7119.s8,PV_RunJoin_ValidatorCell7119.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell7119.s10,PV_RunJoin_ValidatorCell7119.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell7119.s12,PV_RunJoin_ValidatorCell7119.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell7119.s14,PV_RunJoin_ValidatorCell7119.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell7119.s16,PV_RunJoin_ValidatorCell7119.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell7119.s18,PV_RunJoin_ValidatorCell7119.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell7119.s20,PV_RunJoin_ValidatorCell7119.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell7119.s22,PV_RunJoin_ValidatorCell7119.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell7119
