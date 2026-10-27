import R1Z.PV_RunJoin_BankCertificate19
import R1Z.PV_RunJoin_ValidatorCell0019
import R1Z.PV_RunJoin_ValidatorGroup0119
import R1Z.PV_RunJoin_ValidatorGroup0419
import R1Z.PV_RunJoin_ValidatorGroup0719
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell0019
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [11#u32,28#u32,45#u32,62#u32,79#u32,96#u32,113#u32,130#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958529#u32,8#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a1 : State := Array.make 16#usize [11#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958529#u32,8#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a2 : State := Array.make 16#usize [11#u32,28#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958529#u32,8#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a3 : State := Array.make 16#usize [11#u32,28#u32,45#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958529#u32,8#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a4 : State := Array.make 16#usize [11#u32,28#u32,45#u32,62#u32,0#u32,0#u32,0#u32,0#u32,1095958529#u32,8#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a5 : State := Array.make 16#usize [11#u32,28#u32,45#u32,62#u32,79#u32,0#u32,0#u32,0#u32,1095958529#u32,8#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a6 : State := Array.make 16#usize [11#u32,28#u32,45#u32,62#u32,79#u32,96#u32,0#u32,0#u32,1095958529#u32,8#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a7 : State := Array.make 16#usize [11#u32,28#u32,45#u32,62#u32,79#u32,96#u32,113#u32,0#u32,1095958529#u32,8#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a8 : State := Array.make 16#usize [11#u32,28#u32,45#u32,62#u32,79#u32,96#u32,113#u32,130#u32,1095958529#u32,8#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
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
  | 0 => PV_RunJoin_ValidatorCell0019.s0
  | 1 => PV_RunJoin_ValidatorCell0019.s3
  | 2 => PV_RunJoin_ValidatorCell0019.s5
  | 3 => PV_RunJoin_ValidatorCell0019.s7
  | 4 => PV_RunJoin_ValidatorCell0019.s9
  | 5 => PV_RunJoin_ValidatorCell0019.s11
  | 6 => PV_RunJoin_ValidatorCell0019.s13
  | 7 => PV_RunJoin_ValidatorCell0019.s15
  | 8 => PV_RunJoin_ValidatorCell0019.s17
  | 9 => PV_RunJoin_ValidatorCell0019.s19
  | 10 => PV_RunJoin_ValidatorCell0019.s21
  | 11 => PV_RunJoin_ValidatorCell0019.s23
  | _ => PV_RunJoin_ValidatorCell0019.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨11#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨28#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨45#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨62#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨79#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨96#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨113#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨130#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell0019.s2,PV_RunJoin_ValidatorCell0019.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell0019.s4,PV_RunJoin_ValidatorCell0019.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell0019.s6,PV_RunJoin_ValidatorCell0019.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell0019.s8,PV_RunJoin_ValidatorCell0019.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell0019.s10,PV_RunJoin_ValidatorCell0019.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell0019.s12,PV_RunJoin_ValidatorCell0019.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell0019.s14,PV_RunJoin_ValidatorCell0019.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell0019.s16,PV_RunJoin_ValidatorCell0019.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell0019.s18,PV_RunJoin_ValidatorCell0019.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell0019.s20,PV_RunJoin_ValidatorCell0019.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell0019.s22,PV_RunJoin_ValidatorCell0019.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell0019

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell0119
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1486807216#u32,1467982248#u32,80349639#u32,1192110506#u32,1634615995#u32,1246489663#u32,1034489029#u32,2134040966#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a1 : State := Array.make 16#usize [1486807216#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a2 : State := Array.make 16#usize [1486807216#u32,1467982248#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a3 : State := Array.make 16#usize [1486807216#u32,1467982248#u32,80349639#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a4 : State := Array.make 16#usize [1486807216#u32,1467982248#u32,80349639#u32,1192110506#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a5 : State := Array.make 16#usize [1486807216#u32,1467982248#u32,80349639#u32,1192110506#u32,1634615995#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a6 : State := Array.make 16#usize [1486807216#u32,1467982248#u32,80349639#u32,1192110506#u32,1634615995#u32,1246489663#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a7 : State := Array.make 16#usize [1486807216#u32,1467982248#u32,80349639#u32,1192110506#u32,1634615995#u32,1246489663#u32,1034489029#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a8 : State := Array.make 16#usize [1486807216#u32,1467982248#u32,80349639#u32,1192110506#u32,1634615995#u32,1246489663#u32,1034489029#u32,2134040966#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
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
  | 0 => PV_RunJoin_ValidatorCell0119.s0
  | 1 => PV_RunJoin_ValidatorCell0119.s3
  | 2 => PV_RunJoin_ValidatorCell0119.s5
  | 3 => PV_RunJoin_ValidatorCell0119.s7
  | 4 => PV_RunJoin_ValidatorCell0119.s9
  | 5 => PV_RunJoin_ValidatorCell0119.s11
  | 6 => PV_RunJoin_ValidatorCell0119.s13
  | 7 => PV_RunJoin_ValidatorCell0119.s15
  | 8 => PV_RunJoin_ValidatorCell0119.s17
  | 9 => PV_RunJoin_ValidatorCell0119.s19
  | 10 => PV_RunJoin_ValidatorCell0119.s21
  | 11 => PV_RunJoin_ValidatorCell0119.s23
  | _ => PV_RunJoin_ValidatorCell0119.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1486807216#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1467982248#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨80349639#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1192110506#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1634615995#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1246489663#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1034489029#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2134040966#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell0119.s2,PV_RunJoin_ValidatorCell0119.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell0119.s4,PV_RunJoin_ValidatorCell0119.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell0119.s6,PV_RunJoin_ValidatorCell0119.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell0119.s8,PV_RunJoin_ValidatorCell0119.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell0119.s10,PV_RunJoin_ValidatorCell0119.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell0119.s12,PV_RunJoin_ValidatorCell0119.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell0119.s14,PV_RunJoin_ValidatorCell0119.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell0119.s16,PV_RunJoin_ValidatorCell0119.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell0119.s18,PV_RunJoin_ValidatorCell0119.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell0119.s20,PV_RunJoin_ValidatorCell0119.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell0119.s22,PV_RunJoin_ValidatorCell0119.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell0119

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell0219
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1000#u32,77#u32,101#u32,118#u32,135#u32,152#u32,169#u32,186#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [1946206803#u32,48538015#u32,696994726#u32,1059389847#u32,1447429399#u32,645037116#u32,548601256#u32,1757160991#u32,810523887#u32,1816883202#u32,718849816#u32,1097309788#u32,53346212#u32,255319321#u32,163548979#u32,897757192#u32]
def a1 : State := Array.make 16#usize [1946207803#u32,48538015#u32,696994726#u32,1059389847#u32,1447429399#u32,645037116#u32,548601256#u32,1757160991#u32,810523887#u32,1816883202#u32,718849816#u32,1097309788#u32,53346212#u32,255319321#u32,163548979#u32,897757192#u32]
def a2 : State := Array.make 16#usize [1946207803#u32,48538092#u32,696994726#u32,1059389847#u32,1447429399#u32,645037116#u32,548601256#u32,1757160991#u32,810523887#u32,1816883202#u32,718849816#u32,1097309788#u32,53346212#u32,255319321#u32,163548979#u32,897757192#u32]
def a3 : State := Array.make 16#usize [1946207803#u32,48538092#u32,696994827#u32,1059389847#u32,1447429399#u32,645037116#u32,548601256#u32,1757160991#u32,810523887#u32,1816883202#u32,718849816#u32,1097309788#u32,53346212#u32,255319321#u32,163548979#u32,897757192#u32]
def a4 : State := Array.make 16#usize [1946207803#u32,48538092#u32,696994827#u32,1059389965#u32,1447429399#u32,645037116#u32,548601256#u32,1757160991#u32,810523887#u32,1816883202#u32,718849816#u32,1097309788#u32,53346212#u32,255319321#u32,163548979#u32,897757192#u32]
def a5 : State := Array.make 16#usize [1946207803#u32,48538092#u32,696994827#u32,1059389965#u32,1447429534#u32,645037116#u32,548601256#u32,1757160991#u32,810523887#u32,1816883202#u32,718849816#u32,1097309788#u32,53346212#u32,255319321#u32,163548979#u32,897757192#u32]
def a6 : State := Array.make 16#usize [1946207803#u32,48538092#u32,696994827#u32,1059389965#u32,1447429534#u32,645037268#u32,548601256#u32,1757160991#u32,810523887#u32,1816883202#u32,718849816#u32,1097309788#u32,53346212#u32,255319321#u32,163548979#u32,897757192#u32]
def a7 : State := Array.make 16#usize [1946207803#u32,48538092#u32,696994827#u32,1059389965#u32,1447429534#u32,645037268#u32,548601425#u32,1757160991#u32,810523887#u32,1816883202#u32,718849816#u32,1097309788#u32,53346212#u32,255319321#u32,163548979#u32,897757192#u32]
def a8 : State := Array.make 16#usize [1946207803#u32,48538092#u32,696994827#u32,1059389965#u32,1447429534#u32,645037268#u32,548601425#u32,1757161177#u32,810523887#u32,1816883202#u32,718849816#u32,1097309788#u32,53346212#u32,255319321#u32,163548979#u32,897757192#u32]
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
  | 0 => PV_RunJoin_ValidatorCell0219.s0
  | 1 => PV_RunJoin_ValidatorCell0219.s3
  | 2 => PV_RunJoin_ValidatorCell0219.s5
  | 3 => PV_RunJoin_ValidatorCell0219.s7
  | 4 => PV_RunJoin_ValidatorCell0219.s9
  | 5 => PV_RunJoin_ValidatorCell0219.s11
  | 6 => PV_RunJoin_ValidatorCell0219.s13
  | 7 => PV_RunJoin_ValidatorCell0219.s15
  | 8 => PV_RunJoin_ValidatorCell0219.s17
  | 9 => PV_RunJoin_ValidatorCell0219.s19
  | 10 => PV_RunJoin_ValidatorCell0219.s21
  | 11 => PV_RunJoin_ValidatorCell0219.s23
  | _ => PV_RunJoin_ValidatorCell0219.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1946207803#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨48538092#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨696994827#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1059389965#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1447429534#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨645037268#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨548601425#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1757161177#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell0219.s2,PV_RunJoin_ValidatorCell0219.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell0219.s4,PV_RunJoin_ValidatorCell0219.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell0219.s6,PV_RunJoin_ValidatorCell0219.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell0219.s8,PV_RunJoin_ValidatorCell0219.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell0219.s10,PV_RunJoin_ValidatorCell0219.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell0219.s12,PV_RunJoin_ValidatorCell0219.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell0219.s14,PV_RunJoin_ValidatorCell0219.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell0219.s16,PV_RunJoin_ValidatorCell0219.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell0219.s18,PV_RunJoin_ValidatorCell0219.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell0219.s20,PV_RunJoin_ValidatorCell0219.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell0219.s22,PV_RunJoin_ValidatorCell0219.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell0219

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell0319
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [203#u32,220#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [405419764#u32,1027628538#u32,1140951105#u32,1729111010#u32,2021606037#u32,1836155018#u32,2082386700#u32,1774696272#u32,1370644119#u32,1555755447#u32,720886835#u32,429669998#u32,140531686#u32,1776788274#u32,649735172#u32,1287248828#u32]
def a1 : State := Array.make 16#usize [405419967#u32,1027628538#u32,1140951105#u32,1729111010#u32,2021606037#u32,1836155018#u32,2082386700#u32,1774696272#u32,1370644119#u32,1555755447#u32,720886835#u32,429669998#u32,140531686#u32,1776788274#u32,649735172#u32,1287248828#u32]
def a2 : State := Array.make 16#usize [405419967#u32,1027628758#u32,1140951105#u32,1729111010#u32,2021606037#u32,1836155018#u32,2082386700#u32,1774696272#u32,1370644119#u32,1555755447#u32,720886835#u32,429669998#u32,140531686#u32,1776788274#u32,649735172#u32,1287248828#u32]
def a3 : State := Array.make 16#usize [405419967#u32,1027628758#u32,1140951105#u32,1729111010#u32,2021606037#u32,1836155018#u32,2082386700#u32,1774696272#u32,1370644119#u32,1555755447#u32,720886835#u32,429669998#u32,140531686#u32,1776788274#u32,649735172#u32,1287248828#u32]
def a4 : State := Array.make 16#usize [405419967#u32,1027628758#u32,1140951105#u32,1729111010#u32,2021606037#u32,1836155018#u32,2082386700#u32,1774696272#u32,1370644119#u32,1555755447#u32,720886835#u32,429669998#u32,140531686#u32,1776788274#u32,649735172#u32,1287248828#u32]
def a5 : State := Array.make 16#usize [405419967#u32,1027628758#u32,1140951105#u32,1729111010#u32,2021606037#u32,1836155018#u32,2082386700#u32,1774696272#u32,1370644119#u32,1555755447#u32,720886835#u32,429669998#u32,140531686#u32,1776788274#u32,649735172#u32,1287248828#u32]
def a6 : State := Array.make 16#usize [405419967#u32,1027628758#u32,1140951105#u32,1729111010#u32,2021606037#u32,1836155018#u32,2082386700#u32,1774696272#u32,1370644119#u32,1555755447#u32,720886835#u32,429669998#u32,140531686#u32,1776788274#u32,649735172#u32,1287248828#u32]
def a7 : State := Array.make 16#usize [405419967#u32,1027628758#u32,1140951105#u32,1729111010#u32,2021606037#u32,1836155018#u32,2082386700#u32,1774696272#u32,1370644119#u32,1555755447#u32,720886835#u32,429669998#u32,140531686#u32,1776788274#u32,649735172#u32,1287248828#u32]
def a8 : State := Array.make 16#usize [405419967#u32,1027628758#u32,1140951105#u32,1729111010#u32,2021606037#u32,1836155018#u32,2082386700#u32,1774696272#u32,1370644119#u32,1555755447#u32,720886835#u32,429669998#u32,140531686#u32,1776788274#u32,649735172#u32,1287248828#u32]
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
  | 0 => PV_RunJoin_ValidatorCell0319.s0
  | 1 => PV_RunJoin_ValidatorCell0319.s3
  | 2 => PV_RunJoin_ValidatorCell0319.s5
  | 3 => PV_RunJoin_ValidatorCell0319.s7
  | 4 => PV_RunJoin_ValidatorCell0319.s9
  | 5 => PV_RunJoin_ValidatorCell0319.s11
  | 6 => PV_RunJoin_ValidatorCell0319.s13
  | 7 => PV_RunJoin_ValidatorCell0319.s15
  | 8 => PV_RunJoin_ValidatorCell0319.s17
  | 9 => PV_RunJoin_ValidatorCell0319.s19
  | 10 => PV_RunJoin_ValidatorCell0319.s21
  | 11 => PV_RunJoin_ValidatorCell0319.s23
  | _ => PV_RunJoin_ValidatorCell0319.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨405419967#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1027628758#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1140951105#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1729111010#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2021606037#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1836155018#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2082386700#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1774696272#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell0319.s2,PV_RunJoin_ValidatorCell0319.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell0319.s4,PV_RunJoin_ValidatorCell0319.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell0319.s6,PV_RunJoin_ValidatorCell0319.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell0319.s8,PV_RunJoin_ValidatorCell0319.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell0319.s10,PV_RunJoin_ValidatorCell0319.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell0319.s12,PV_RunJoin_ValidatorCell0319.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell0319.s14,PV_RunJoin_ValidatorCell0319.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell0319.s16,PV_RunJoin_ValidatorCell0319.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell0319.s18,PV_RunJoin_ValidatorCell0319.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell0319.s20,PV_RunJoin_ValidatorCell0319.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell0319.s22,PV_RunJoin_ValidatorCell0319.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell0319

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell0419
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [11#u32,28#u32,45#u32,62#u32,79#u32,96#u32,113#u32,130#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958530#u32,16#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a1 : State := Array.make 16#usize [11#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958530#u32,16#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a2 : State := Array.make 16#usize [11#u32,28#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958530#u32,16#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a3 : State := Array.make 16#usize [11#u32,28#u32,45#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958530#u32,16#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a4 : State := Array.make 16#usize [11#u32,28#u32,45#u32,62#u32,0#u32,0#u32,0#u32,0#u32,1095958530#u32,16#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a5 : State := Array.make 16#usize [11#u32,28#u32,45#u32,62#u32,79#u32,0#u32,0#u32,0#u32,1095958530#u32,16#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a6 : State := Array.make 16#usize [11#u32,28#u32,45#u32,62#u32,79#u32,96#u32,0#u32,0#u32,1095958530#u32,16#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a7 : State := Array.make 16#usize [11#u32,28#u32,45#u32,62#u32,79#u32,96#u32,113#u32,0#u32,1095958530#u32,16#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a8 : State := Array.make 16#usize [11#u32,28#u32,45#u32,62#u32,79#u32,96#u32,113#u32,130#u32,1095958530#u32,16#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
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
  | 0 => PV_RunJoin_ValidatorCell0419.s0
  | 1 => PV_RunJoin_ValidatorCell0419.s3
  | 2 => PV_RunJoin_ValidatorCell0419.s5
  | 3 => PV_RunJoin_ValidatorCell0419.s7
  | 4 => PV_RunJoin_ValidatorCell0419.s9
  | 5 => PV_RunJoin_ValidatorCell0419.s11
  | 6 => PV_RunJoin_ValidatorCell0419.s13
  | 7 => PV_RunJoin_ValidatorCell0419.s15
  | 8 => PV_RunJoin_ValidatorCell0419.s17
  | 9 => PV_RunJoin_ValidatorCell0419.s19
  | 10 => PV_RunJoin_ValidatorCell0419.s21
  | 11 => PV_RunJoin_ValidatorCell0419.s23
  | _ => PV_RunJoin_ValidatorCell0419.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨11#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨28#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨45#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨62#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨79#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨96#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨113#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨130#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell0419.s2,PV_RunJoin_ValidatorCell0419.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell0419.s4,PV_RunJoin_ValidatorCell0419.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell0419.s6,PV_RunJoin_ValidatorCell0419.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell0419.s8,PV_RunJoin_ValidatorCell0419.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell0419.s10,PV_RunJoin_ValidatorCell0419.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell0419.s12,PV_RunJoin_ValidatorCell0419.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell0419.s14,PV_RunJoin_ValidatorCell0419.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell0419.s16,PV_RunJoin_ValidatorCell0419.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell0419.s18,PV_RunJoin_ValidatorCell0419.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell0419.s20,PV_RunJoin_ValidatorCell0419.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell0419.s22,PV_RunJoin_ValidatorCell0419.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell0419

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell0519
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [101#u32,118#u32,135#u32,152#u32,169#u32,186#u32,203#u32,220#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [1509501854#u32,1054326288#u32,990027500#u32,639862859#u32,434148632#u32,2026900882#u32,821792967#u32,1955070469#u32,2126048206#u32,1654414616#u32,1959107133#u32,943087239#u32,609987601#u32,1346814918#u32,58140128#u32,1000734734#u32]
def a1 : State := Array.make 16#usize [1509501955#u32,1054326288#u32,990027500#u32,639862859#u32,434148632#u32,2026900882#u32,821792967#u32,1955070469#u32,2126048206#u32,1654414616#u32,1959107133#u32,943087239#u32,609987601#u32,1346814918#u32,58140128#u32,1000734734#u32]
def a2 : State := Array.make 16#usize [1509501955#u32,1054326406#u32,990027500#u32,639862859#u32,434148632#u32,2026900882#u32,821792967#u32,1955070469#u32,2126048206#u32,1654414616#u32,1959107133#u32,943087239#u32,609987601#u32,1346814918#u32,58140128#u32,1000734734#u32]
def a3 : State := Array.make 16#usize [1509501955#u32,1054326406#u32,990027635#u32,639862859#u32,434148632#u32,2026900882#u32,821792967#u32,1955070469#u32,2126048206#u32,1654414616#u32,1959107133#u32,943087239#u32,609987601#u32,1346814918#u32,58140128#u32,1000734734#u32]
def a4 : State := Array.make 16#usize [1509501955#u32,1054326406#u32,990027635#u32,639863011#u32,434148632#u32,2026900882#u32,821792967#u32,1955070469#u32,2126048206#u32,1654414616#u32,1959107133#u32,943087239#u32,609987601#u32,1346814918#u32,58140128#u32,1000734734#u32]
def a5 : State := Array.make 16#usize [1509501955#u32,1054326406#u32,990027635#u32,639863011#u32,434148801#u32,2026900882#u32,821792967#u32,1955070469#u32,2126048206#u32,1654414616#u32,1959107133#u32,943087239#u32,609987601#u32,1346814918#u32,58140128#u32,1000734734#u32]
def a6 : State := Array.make 16#usize [1509501955#u32,1054326406#u32,990027635#u32,639863011#u32,434148801#u32,2026901068#u32,821792967#u32,1955070469#u32,2126048206#u32,1654414616#u32,1959107133#u32,943087239#u32,609987601#u32,1346814918#u32,58140128#u32,1000734734#u32]
def a7 : State := Array.make 16#usize [1509501955#u32,1054326406#u32,990027635#u32,639863011#u32,434148801#u32,2026901068#u32,821793170#u32,1955070469#u32,2126048206#u32,1654414616#u32,1959107133#u32,943087239#u32,609987601#u32,1346814918#u32,58140128#u32,1000734734#u32]
def a8 : State := Array.make 16#usize [1509501955#u32,1054326406#u32,990027635#u32,639863011#u32,434148801#u32,2026901068#u32,821793170#u32,1955070689#u32,2126048206#u32,1654414616#u32,1959107133#u32,943087239#u32,609987601#u32,1346814918#u32,58140128#u32,1000734734#u32]
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
  | 0 => PV_RunJoin_ValidatorCell0519.s0
  | 1 => PV_RunJoin_ValidatorCell0519.s3
  | 2 => PV_RunJoin_ValidatorCell0519.s5
  | 3 => PV_RunJoin_ValidatorCell0519.s7
  | 4 => PV_RunJoin_ValidatorCell0519.s9
  | 5 => PV_RunJoin_ValidatorCell0519.s11
  | 6 => PV_RunJoin_ValidatorCell0519.s13
  | 7 => PV_RunJoin_ValidatorCell0519.s15
  | 8 => PV_RunJoin_ValidatorCell0519.s17
  | 9 => PV_RunJoin_ValidatorCell0519.s19
  | 10 => PV_RunJoin_ValidatorCell0519.s21
  | 11 => PV_RunJoin_ValidatorCell0519.s23
  | _ => PV_RunJoin_ValidatorCell0519.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1509501955#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1054326406#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨990027635#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨639863011#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨434148801#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2026901068#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨821793170#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1955070689#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell0519.s2,PV_RunJoin_ValidatorCell0519.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell0519.s4,PV_RunJoin_ValidatorCell0519.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell0519.s6,PV_RunJoin_ValidatorCell0519.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell0519.s8,PV_RunJoin_ValidatorCell0519.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell0519.s10,PV_RunJoin_ValidatorCell0519.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell0519.s12,PV_RunJoin_ValidatorCell0519.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell0519.s14,PV_RunJoin_ValidatorCell0519.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell0519.s16,PV_RunJoin_ValidatorCell0519.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell0519.s18,PV_RunJoin_ValidatorCell0519.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell0519.s20,PV_RunJoin_ValidatorCell0519.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell0519.s22,PV_RunJoin_ValidatorCell0519.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell0519

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell0619
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [2028667570#u32,45893279#u32,894642502#u32,1930282162#u32,1562116262#u32,823639309#u32,745717450#u32,1034934647#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,901#u32,918#u32,935#u32,952#u32,969#u32,986#u32,1003#u32,1095963649#u32]
def a1 : State := Array.make 16#usize [2028667570#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,901#u32,918#u32,935#u32,952#u32,969#u32,986#u32,1003#u32,1095963649#u32]
def a2 : State := Array.make 16#usize [2028667570#u32,45893279#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,901#u32,918#u32,935#u32,952#u32,969#u32,986#u32,1003#u32,1095963649#u32]
def a3 : State := Array.make 16#usize [2028667570#u32,45893279#u32,894642502#u32,0#u32,0#u32,0#u32,0#u32,0#u32,901#u32,918#u32,935#u32,952#u32,969#u32,986#u32,1003#u32,1095963649#u32]
def a4 : State := Array.make 16#usize [2028667570#u32,45893279#u32,894642502#u32,1930282162#u32,0#u32,0#u32,0#u32,0#u32,901#u32,918#u32,935#u32,952#u32,969#u32,986#u32,1003#u32,1095963649#u32]
def a5 : State := Array.make 16#usize [2028667570#u32,45893279#u32,894642502#u32,1930282162#u32,1562116262#u32,0#u32,0#u32,0#u32,901#u32,918#u32,935#u32,952#u32,969#u32,986#u32,1003#u32,1095963649#u32]
def a6 : State := Array.make 16#usize [2028667570#u32,45893279#u32,894642502#u32,1930282162#u32,1562116262#u32,823639309#u32,0#u32,0#u32,901#u32,918#u32,935#u32,952#u32,969#u32,986#u32,1003#u32,1095963649#u32]
def a7 : State := Array.make 16#usize [2028667570#u32,45893279#u32,894642502#u32,1930282162#u32,1562116262#u32,823639309#u32,745717450#u32,0#u32,901#u32,918#u32,935#u32,952#u32,969#u32,986#u32,1003#u32,1095963649#u32]
def a8 : State := Array.make 16#usize [2028667570#u32,45893279#u32,894642502#u32,1930282162#u32,1562116262#u32,823639309#u32,745717450#u32,1034934647#u32,901#u32,918#u32,935#u32,952#u32,969#u32,986#u32,1003#u32,1095963649#u32]
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
  | 0 => PV_RunJoin_ValidatorCell0619.s0
  | 1 => PV_RunJoin_ValidatorCell0619.s3
  | 2 => PV_RunJoin_ValidatorCell0619.s5
  | 3 => PV_RunJoin_ValidatorCell0619.s7
  | 4 => PV_RunJoin_ValidatorCell0619.s9
  | 5 => PV_RunJoin_ValidatorCell0619.s11
  | 6 => PV_RunJoin_ValidatorCell0619.s13
  | 7 => PV_RunJoin_ValidatorCell0619.s15
  | 8 => PV_RunJoin_ValidatorCell0619.s17
  | 9 => PV_RunJoin_ValidatorCell0619.s19
  | 10 => PV_RunJoin_ValidatorCell0619.s21
  | 11 => PV_RunJoin_ValidatorCell0619.s23
  | _ => PV_RunJoin_ValidatorCell0619.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨2028667570#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨45893279#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨894642502#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1930282162#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1562116262#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨823639309#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨745717450#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1034934647#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell0619.s2,PV_RunJoin_ValidatorCell0619.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell0619.s4,PV_RunJoin_ValidatorCell0619.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell0619.s6,PV_RunJoin_ValidatorCell0619.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell0619.s8,PV_RunJoin_ValidatorCell0619.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell0619.s10,PV_RunJoin_ValidatorCell0619.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell0619.s12,PV_RunJoin_ValidatorCell0619.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell0619.s14,PV_RunJoin_ValidatorCell0619.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell0619.s16,PV_RunJoin_ValidatorCell0619.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell0619.s18,PV_RunJoin_ValidatorCell0619.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell0619.s20,PV_RunJoin_ValidatorCell0619.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell0619.s22,PV_RunJoin_ValidatorCell0619.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell0619

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell0719
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [2001#u32,2018#u32,2035#u32,2052#u32,2069#u32,2086#u32,2103#u32,2120#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1055864870#u32,1015153496#u32,899228473#u32,2043224478#u32,1075657363#u32,1804637297#u32,712143154#u32,104841626#u32]
def a1 : State := Array.make 16#usize [2001#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1055864870#u32,1015153496#u32,899228473#u32,2043224478#u32,1075657363#u32,1804637297#u32,712143154#u32,104841626#u32]
def a2 : State := Array.make 16#usize [2001#u32,2018#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1055864870#u32,1015153496#u32,899228473#u32,2043224478#u32,1075657363#u32,1804637297#u32,712143154#u32,104841626#u32]
def a3 : State := Array.make 16#usize [2001#u32,2018#u32,2035#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1055864870#u32,1015153496#u32,899228473#u32,2043224478#u32,1075657363#u32,1804637297#u32,712143154#u32,104841626#u32]
def a4 : State := Array.make 16#usize [2001#u32,2018#u32,2035#u32,2052#u32,0#u32,0#u32,0#u32,0#u32,1055864870#u32,1015153496#u32,899228473#u32,2043224478#u32,1075657363#u32,1804637297#u32,712143154#u32,104841626#u32]
def a5 : State := Array.make 16#usize [2001#u32,2018#u32,2035#u32,2052#u32,2069#u32,0#u32,0#u32,0#u32,1055864870#u32,1015153496#u32,899228473#u32,2043224478#u32,1075657363#u32,1804637297#u32,712143154#u32,104841626#u32]
def a6 : State := Array.make 16#usize [2001#u32,2018#u32,2035#u32,2052#u32,2069#u32,2086#u32,0#u32,0#u32,1055864870#u32,1015153496#u32,899228473#u32,2043224478#u32,1075657363#u32,1804637297#u32,712143154#u32,104841626#u32]
def a7 : State := Array.make 16#usize [2001#u32,2018#u32,2035#u32,2052#u32,2069#u32,2086#u32,2103#u32,0#u32,1055864870#u32,1015153496#u32,899228473#u32,2043224478#u32,1075657363#u32,1804637297#u32,712143154#u32,104841626#u32]
def a8 : State := Array.make 16#usize [2001#u32,2018#u32,2035#u32,2052#u32,2069#u32,2086#u32,2103#u32,2120#u32,1055864870#u32,1015153496#u32,899228473#u32,2043224478#u32,1075657363#u32,1804637297#u32,712143154#u32,104841626#u32]
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
  | 0 => PV_RunJoin_ValidatorCell0719.s0
  | 1 => PV_RunJoin_ValidatorCell0719.s3
  | 2 => PV_RunJoin_ValidatorCell0719.s5
  | 3 => PV_RunJoin_ValidatorCell0719.s7
  | 4 => PV_RunJoin_ValidatorCell0719.s9
  | 5 => PV_RunJoin_ValidatorCell0719.s11
  | 6 => PV_RunJoin_ValidatorCell0719.s13
  | 7 => PV_RunJoin_ValidatorCell0719.s15
  | 8 => PV_RunJoin_ValidatorCell0719.s17
  | 9 => PV_RunJoin_ValidatorCell0719.s19
  | 10 => PV_RunJoin_ValidatorCell0719.s21
  | 11 => PV_RunJoin_ValidatorCell0719.s23
  | _ => PV_RunJoin_ValidatorCell0719.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨2001#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2018#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2035#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2052#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2069#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2086#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2103#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2120#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell0719.s2,PV_RunJoin_ValidatorCell0719.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell0719.s4,PV_RunJoin_ValidatorCell0719.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell0719.s6,PV_RunJoin_ValidatorCell0719.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell0719.s8,PV_RunJoin_ValidatorCell0719.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell0719.s10,PV_RunJoin_ValidatorCell0719.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell0719.s12,PV_RunJoin_ValidatorCell0719.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell0719.s14,PV_RunJoin_ValidatorCell0719.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell0719.s16,PV_RunJoin_ValidatorCell0719.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell0719.s18,PV_RunJoin_ValidatorCell0719.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell0719.s20,PV_RunJoin_ValidatorCell0719.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell0719.s22,PV_RunJoin_ValidatorCell0719.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell0719

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell0819
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1292573235#u32,1255372443#u32,1043307233#u32,1891352131#u32,920017154#u32,1033317521#u32,170537605#u32,505604950#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2021#u32,2038#u32,2055#u32,2072#u32,2089#u32,2106#u32,2123#u32,1095964769#u32]
def a1 : State := Array.make 16#usize [1292573235#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2021#u32,2038#u32,2055#u32,2072#u32,2089#u32,2106#u32,2123#u32,1095964769#u32]
def a2 : State := Array.make 16#usize [1292573235#u32,1255372443#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2021#u32,2038#u32,2055#u32,2072#u32,2089#u32,2106#u32,2123#u32,1095964769#u32]
def a3 : State := Array.make 16#usize [1292573235#u32,1255372443#u32,1043307233#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2021#u32,2038#u32,2055#u32,2072#u32,2089#u32,2106#u32,2123#u32,1095964769#u32]
def a4 : State := Array.make 16#usize [1292573235#u32,1255372443#u32,1043307233#u32,1891352131#u32,0#u32,0#u32,0#u32,0#u32,2021#u32,2038#u32,2055#u32,2072#u32,2089#u32,2106#u32,2123#u32,1095964769#u32]
def a5 : State := Array.make 16#usize [1292573235#u32,1255372443#u32,1043307233#u32,1891352131#u32,920017154#u32,0#u32,0#u32,0#u32,2021#u32,2038#u32,2055#u32,2072#u32,2089#u32,2106#u32,2123#u32,1095964769#u32]
def a6 : State := Array.make 16#usize [1292573235#u32,1255372443#u32,1043307233#u32,1891352131#u32,920017154#u32,1033317521#u32,0#u32,0#u32,2021#u32,2038#u32,2055#u32,2072#u32,2089#u32,2106#u32,2123#u32,1095964769#u32]
def a7 : State := Array.make 16#usize [1292573235#u32,1255372443#u32,1043307233#u32,1891352131#u32,920017154#u32,1033317521#u32,170537605#u32,0#u32,2021#u32,2038#u32,2055#u32,2072#u32,2089#u32,2106#u32,2123#u32,1095964769#u32]
def a8 : State := Array.make 16#usize [1292573235#u32,1255372443#u32,1043307233#u32,1891352131#u32,920017154#u32,1033317521#u32,170537605#u32,505604950#u32,2021#u32,2038#u32,2055#u32,2072#u32,2089#u32,2106#u32,2123#u32,1095964769#u32]
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
  | 0 => PV_RunJoin_ValidatorCell0819.s0
  | 1 => PV_RunJoin_ValidatorCell0819.s3
  | 2 => PV_RunJoin_ValidatorCell0819.s5
  | 3 => PV_RunJoin_ValidatorCell0819.s7
  | 4 => PV_RunJoin_ValidatorCell0819.s9
  | 5 => PV_RunJoin_ValidatorCell0819.s11
  | 6 => PV_RunJoin_ValidatorCell0819.s13
  | 7 => PV_RunJoin_ValidatorCell0819.s15
  | 8 => PV_RunJoin_ValidatorCell0819.s17
  | 9 => PV_RunJoin_ValidatorCell0819.s19
  | 10 => PV_RunJoin_ValidatorCell0819.s21
  | 11 => PV_RunJoin_ValidatorCell0819.s23
  | _ => PV_RunJoin_ValidatorCell0819.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1292573235#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1255372443#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1043307233#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1891352131#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨920017154#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1033317521#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨170537605#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨505604950#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell0819.s2,PV_RunJoin_ValidatorCell0819.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell0819.s4,PV_RunJoin_ValidatorCell0819.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell0819.s6,PV_RunJoin_ValidatorCell0819.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell0819.s8,PV_RunJoin_ValidatorCell0819.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell0819.s10,PV_RunJoin_ValidatorCell0819.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell0819.s12,PV_RunJoin_ValidatorCell0819.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell0819.s14,PV_RunJoin_ValidatorCell0819.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell0819.s16,PV_RunJoin_ValidatorCell0819.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell0819.s18,PV_RunJoin_ValidatorCell0819.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell0819.s20,PV_RunJoin_ValidatorCell0819.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell0819.s22,PV_RunJoin_ValidatorCell0819.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell0819
