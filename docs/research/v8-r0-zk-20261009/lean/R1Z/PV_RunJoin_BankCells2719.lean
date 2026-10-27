import R1Z.PV_RunJoin_BankCertificate19
import R1Z.PV_RunJoin_ValidatorGroup2519
import R1Z.PV_RunJoin_ValidatorGroup2819
import R1Z.PV_RunJoin_ValidatorGroup3119
import R1Z.PV_RunJoin_ValidatorGroup3419
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell2719
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [3001#u32,3018#u32,3035#u32,3052#u32,3069#u32,3086#u32,3103#u32,3120#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,9991919#u32,1366070145#u32,2057247444#u32,1742688934#u32,729806222#u32,499041299#u32,1681224112#u32,433910735#u32]
def a1 : State := Array.make 16#usize [3001#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,9991919#u32,1366070145#u32,2057247444#u32,1742688934#u32,729806222#u32,499041299#u32,1681224112#u32,433910735#u32]
def a2 : State := Array.make 16#usize [3001#u32,3018#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,9991919#u32,1366070145#u32,2057247444#u32,1742688934#u32,729806222#u32,499041299#u32,1681224112#u32,433910735#u32]
def a3 : State := Array.make 16#usize [3001#u32,3018#u32,3035#u32,0#u32,0#u32,0#u32,0#u32,0#u32,9991919#u32,1366070145#u32,2057247444#u32,1742688934#u32,729806222#u32,499041299#u32,1681224112#u32,433910735#u32]
def a4 : State := Array.make 16#usize [3001#u32,3018#u32,3035#u32,3052#u32,0#u32,0#u32,0#u32,0#u32,9991919#u32,1366070145#u32,2057247444#u32,1742688934#u32,729806222#u32,499041299#u32,1681224112#u32,433910735#u32]
def a5 : State := Array.make 16#usize [3001#u32,3018#u32,3035#u32,3052#u32,3069#u32,0#u32,0#u32,0#u32,9991919#u32,1366070145#u32,2057247444#u32,1742688934#u32,729806222#u32,499041299#u32,1681224112#u32,433910735#u32]
def a6 : State := Array.make 16#usize [3001#u32,3018#u32,3035#u32,3052#u32,3069#u32,3086#u32,0#u32,0#u32,9991919#u32,1366070145#u32,2057247444#u32,1742688934#u32,729806222#u32,499041299#u32,1681224112#u32,433910735#u32]
def a7 : State := Array.make 16#usize [3001#u32,3018#u32,3035#u32,3052#u32,3069#u32,3086#u32,3103#u32,0#u32,9991919#u32,1366070145#u32,2057247444#u32,1742688934#u32,729806222#u32,499041299#u32,1681224112#u32,433910735#u32]
def a8 : State := Array.make 16#usize [3001#u32,3018#u32,3035#u32,3052#u32,3069#u32,3086#u32,3103#u32,3120#u32,9991919#u32,1366070145#u32,2057247444#u32,1742688934#u32,729806222#u32,499041299#u32,1681224112#u32,433910735#u32]
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
  | 0 => PV_RunJoin_ValidatorCell2719.s0
  | 1 => PV_RunJoin_ValidatorCell2719.s3
  | 2 => PV_RunJoin_ValidatorCell2719.s5
  | 3 => PV_RunJoin_ValidatorCell2719.s7
  | 4 => PV_RunJoin_ValidatorCell2719.s9
  | 5 => PV_RunJoin_ValidatorCell2719.s11
  | 6 => PV_RunJoin_ValidatorCell2719.s13
  | 7 => PV_RunJoin_ValidatorCell2719.s15
  | 8 => PV_RunJoin_ValidatorCell2719.s17
  | 9 => PV_RunJoin_ValidatorCell2719.s19
  | 10 => PV_RunJoin_ValidatorCell2719.s21
  | 11 => PV_RunJoin_ValidatorCell2719.s23
  | _ => PV_RunJoin_ValidatorCell2719.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨3001#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨3018#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨3035#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨3052#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨3069#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨3086#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨3103#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨3120#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell2719.s2,PV_RunJoin_ValidatorCell2719.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell2719.s4,PV_RunJoin_ValidatorCell2719.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell2719.s6,PV_RunJoin_ValidatorCell2719.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell2719.s8,PV_RunJoin_ValidatorCell2719.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell2719.s10,PV_RunJoin_ValidatorCell2719.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell2719.s12,PV_RunJoin_ValidatorCell2719.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell2719.s14,PV_RunJoin_ValidatorCell2719.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell2719.s16,PV_RunJoin_ValidatorCell2719.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell2719.s18,PV_RunJoin_ValidatorCell2719.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell2719.s20,PV_RunJoin_ValidatorCell2719.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell2719.s22,PV_RunJoin_ValidatorCell2719.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell2719

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell2819
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1542818520#u32,1882037664#u32,1251951877#u32,1554108809#u32,81746851#u32,159927545#u32,2111428769#u32,132405182#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,3101#u32,3118#u32,3135#u32,3152#u32,3169#u32,3186#u32,3203#u32,1095965849#u32]
def a1 : State := Array.make 16#usize [1542818520#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,3101#u32,3118#u32,3135#u32,3152#u32,3169#u32,3186#u32,3203#u32,1095965849#u32]
def a2 : State := Array.make 16#usize [1542818520#u32,1882037664#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,3101#u32,3118#u32,3135#u32,3152#u32,3169#u32,3186#u32,3203#u32,1095965849#u32]
def a3 : State := Array.make 16#usize [1542818520#u32,1882037664#u32,1251951877#u32,0#u32,0#u32,0#u32,0#u32,0#u32,3101#u32,3118#u32,3135#u32,3152#u32,3169#u32,3186#u32,3203#u32,1095965849#u32]
def a4 : State := Array.make 16#usize [1542818520#u32,1882037664#u32,1251951877#u32,1554108809#u32,0#u32,0#u32,0#u32,0#u32,3101#u32,3118#u32,3135#u32,3152#u32,3169#u32,3186#u32,3203#u32,1095965849#u32]
def a5 : State := Array.make 16#usize [1542818520#u32,1882037664#u32,1251951877#u32,1554108809#u32,81746851#u32,0#u32,0#u32,0#u32,3101#u32,3118#u32,3135#u32,3152#u32,3169#u32,3186#u32,3203#u32,1095965849#u32]
def a6 : State := Array.make 16#usize [1542818520#u32,1882037664#u32,1251951877#u32,1554108809#u32,81746851#u32,159927545#u32,0#u32,0#u32,3101#u32,3118#u32,3135#u32,3152#u32,3169#u32,3186#u32,3203#u32,1095965849#u32]
def a7 : State := Array.make 16#usize [1542818520#u32,1882037664#u32,1251951877#u32,1554108809#u32,81746851#u32,159927545#u32,2111428769#u32,0#u32,3101#u32,3118#u32,3135#u32,3152#u32,3169#u32,3186#u32,3203#u32,1095965849#u32]
def a8 : State := Array.make 16#usize [1542818520#u32,1882037664#u32,1251951877#u32,1554108809#u32,81746851#u32,159927545#u32,2111428769#u32,132405182#u32,3101#u32,3118#u32,3135#u32,3152#u32,3169#u32,3186#u32,3203#u32,1095965849#u32]
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
  | 0 => PV_RunJoin_ValidatorCell2819.s0
  | 1 => PV_RunJoin_ValidatorCell2819.s3
  | 2 => PV_RunJoin_ValidatorCell2819.s5
  | 3 => PV_RunJoin_ValidatorCell2819.s7
  | 4 => PV_RunJoin_ValidatorCell2819.s9
  | 5 => PV_RunJoin_ValidatorCell2819.s11
  | 6 => PV_RunJoin_ValidatorCell2819.s13
  | 7 => PV_RunJoin_ValidatorCell2819.s15
  | 8 => PV_RunJoin_ValidatorCell2819.s17
  | 9 => PV_RunJoin_ValidatorCell2819.s19
  | 10 => PV_RunJoin_ValidatorCell2819.s21
  | 11 => PV_RunJoin_ValidatorCell2819.s23
  | _ => PV_RunJoin_ValidatorCell2819.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1542818520#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1882037664#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1251951877#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1554108809#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨81746851#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨159927545#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2111428769#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨132405182#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell2819.s2,PV_RunJoin_ValidatorCell2819.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell2819.s4,PV_RunJoin_ValidatorCell2819.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell2819.s6,PV_RunJoin_ValidatorCell2819.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell2819.s8,PV_RunJoin_ValidatorCell2819.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell2819.s10,PV_RunJoin_ValidatorCell2819.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell2819.s12,PV_RunJoin_ValidatorCell2819.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell2819.s14,PV_RunJoin_ValidatorCell2819.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell2819.s16,PV_RunJoin_ValidatorCell2819.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell2819.s18,PV_RunJoin_ValidatorCell2819.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell2819.s20,PV_RunJoin_ValidatorCell2819.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell2819.s22,PV_RunJoin_ValidatorCell2819.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell2819

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell2919
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [3201#u32,3218#u32,3235#u32,3252#u32,3269#u32,3286#u32,3303#u32,3320#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,407525056#u32,1458948676#u32,1930040251#u32,1044760048#u32,961029422#u32,441494278#u32,1982425121#u32,317355450#u32]
def a1 : State := Array.make 16#usize [3201#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,407525056#u32,1458948676#u32,1930040251#u32,1044760048#u32,961029422#u32,441494278#u32,1982425121#u32,317355450#u32]
def a2 : State := Array.make 16#usize [3201#u32,3218#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,407525056#u32,1458948676#u32,1930040251#u32,1044760048#u32,961029422#u32,441494278#u32,1982425121#u32,317355450#u32]
def a3 : State := Array.make 16#usize [3201#u32,3218#u32,3235#u32,0#u32,0#u32,0#u32,0#u32,0#u32,407525056#u32,1458948676#u32,1930040251#u32,1044760048#u32,961029422#u32,441494278#u32,1982425121#u32,317355450#u32]
def a4 : State := Array.make 16#usize [3201#u32,3218#u32,3235#u32,3252#u32,0#u32,0#u32,0#u32,0#u32,407525056#u32,1458948676#u32,1930040251#u32,1044760048#u32,961029422#u32,441494278#u32,1982425121#u32,317355450#u32]
def a5 : State := Array.make 16#usize [3201#u32,3218#u32,3235#u32,3252#u32,3269#u32,0#u32,0#u32,0#u32,407525056#u32,1458948676#u32,1930040251#u32,1044760048#u32,961029422#u32,441494278#u32,1982425121#u32,317355450#u32]
def a6 : State := Array.make 16#usize [3201#u32,3218#u32,3235#u32,3252#u32,3269#u32,3286#u32,0#u32,0#u32,407525056#u32,1458948676#u32,1930040251#u32,1044760048#u32,961029422#u32,441494278#u32,1982425121#u32,317355450#u32]
def a7 : State := Array.make 16#usize [3201#u32,3218#u32,3235#u32,3252#u32,3269#u32,3286#u32,3303#u32,0#u32,407525056#u32,1458948676#u32,1930040251#u32,1044760048#u32,961029422#u32,441494278#u32,1982425121#u32,317355450#u32]
def a8 : State := Array.make 16#usize [3201#u32,3218#u32,3235#u32,3252#u32,3269#u32,3286#u32,3303#u32,3320#u32,407525056#u32,1458948676#u32,1930040251#u32,1044760048#u32,961029422#u32,441494278#u32,1982425121#u32,317355450#u32]
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
  | 0 => PV_RunJoin_ValidatorCell2919.s0
  | 1 => PV_RunJoin_ValidatorCell2919.s3
  | 2 => PV_RunJoin_ValidatorCell2919.s5
  | 3 => PV_RunJoin_ValidatorCell2919.s7
  | 4 => PV_RunJoin_ValidatorCell2919.s9
  | 5 => PV_RunJoin_ValidatorCell2919.s11
  | 6 => PV_RunJoin_ValidatorCell2919.s13
  | 7 => PV_RunJoin_ValidatorCell2919.s15
  | 8 => PV_RunJoin_ValidatorCell2919.s17
  | 9 => PV_RunJoin_ValidatorCell2919.s19
  | 10 => PV_RunJoin_ValidatorCell2919.s21
  | 11 => PV_RunJoin_ValidatorCell2919.s23
  | _ => PV_RunJoin_ValidatorCell2919.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨3201#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨3218#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨3235#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨3252#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨3269#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨3286#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨3303#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨3320#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell2919.s2,PV_RunJoin_ValidatorCell2919.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell2919.s4,PV_RunJoin_ValidatorCell2919.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell2919.s6,PV_RunJoin_ValidatorCell2919.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell2919.s8,PV_RunJoin_ValidatorCell2919.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell2919.s10,PV_RunJoin_ValidatorCell2919.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell2919.s12,PV_RunJoin_ValidatorCell2919.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell2919.s14,PV_RunJoin_ValidatorCell2919.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell2919.s16,PV_RunJoin_ValidatorCell2919.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell2919.s18,PV_RunJoin_ValidatorCell2919.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell2919.s20,PV_RunJoin_ValidatorCell2919.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell2919.s22,PV_RunJoin_ValidatorCell2919.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell2919

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell3019
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [301#u32,318#u32,335#u32,352#u32,369#u32,386#u32,403#u32,420#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a1 : State := Array.make 16#usize [301#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a2 : State := Array.make 16#usize [301#u32,318#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a3 : State := Array.make 16#usize [301#u32,318#u32,335#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a4 : State := Array.make 16#usize [301#u32,318#u32,335#u32,352#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a5 : State := Array.make 16#usize [301#u32,318#u32,335#u32,352#u32,369#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a6 : State := Array.make 16#usize [301#u32,318#u32,335#u32,352#u32,369#u32,386#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a7 : State := Array.make 16#usize [301#u32,318#u32,335#u32,352#u32,369#u32,386#u32,403#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a8 : State := Array.make 16#usize [301#u32,318#u32,335#u32,352#u32,369#u32,386#u32,403#u32,420#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
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
  | 0 => PV_RunJoin_ValidatorCell3019.s0
  | 1 => PV_RunJoin_ValidatorCell3019.s3
  | 2 => PV_RunJoin_ValidatorCell3019.s5
  | 3 => PV_RunJoin_ValidatorCell3019.s7
  | 4 => PV_RunJoin_ValidatorCell3019.s9
  | 5 => PV_RunJoin_ValidatorCell3019.s11
  | 6 => PV_RunJoin_ValidatorCell3019.s13
  | 7 => PV_RunJoin_ValidatorCell3019.s15
  | 8 => PV_RunJoin_ValidatorCell3019.s17
  | 9 => PV_RunJoin_ValidatorCell3019.s19
  | 10 => PV_RunJoin_ValidatorCell3019.s21
  | 11 => PV_RunJoin_ValidatorCell3019.s23
  | _ => PV_RunJoin_ValidatorCell3019.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨301#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨318#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨335#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨352#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨369#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨386#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨403#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨420#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell3019.s2,PV_RunJoin_ValidatorCell3019.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell3019.s4,PV_RunJoin_ValidatorCell3019.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell3019.s6,PV_RunJoin_ValidatorCell3019.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell3019.s8,PV_RunJoin_ValidatorCell3019.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell3019.s10,PV_RunJoin_ValidatorCell3019.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell3019.s12,PV_RunJoin_ValidatorCell3019.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell3019.s14,PV_RunJoin_ValidatorCell3019.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell3019.s16,PV_RunJoin_ValidatorCell3019.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell3019.s18,PV_RunJoin_ValidatorCell3019.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell3019.s20,PV_RunJoin_ValidatorCell3019.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell3019.s22,PV_RunJoin_ValidatorCell3019.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell3019

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell3119
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [600#u32,77#u32,401#u32,418#u32,435#u32,452#u32,469#u32,486#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [2142349696#u32,632952015#u32,243019942#u32,1561436836#u32,1020436789#u32,55227704#u32,1354638029#u32,1231398462#u32,1220349109#u32,1514487249#u32,1716044202#u32,1422215276#u32,1882740077#u32,110355981#u32,222565438#u32,2035926413#u32]
def a1 : State := Array.make 16#usize [2142350296#u32,632952015#u32,243019942#u32,1561436836#u32,1020436789#u32,55227704#u32,1354638029#u32,1231398462#u32,1220349109#u32,1514487249#u32,1716044202#u32,1422215276#u32,1882740077#u32,110355981#u32,222565438#u32,2035926413#u32]
def a2 : State := Array.make 16#usize [2142350296#u32,632952092#u32,243019942#u32,1561436836#u32,1020436789#u32,55227704#u32,1354638029#u32,1231398462#u32,1220349109#u32,1514487249#u32,1716044202#u32,1422215276#u32,1882740077#u32,110355981#u32,222565438#u32,2035926413#u32]
def a3 : State := Array.make 16#usize [2142350296#u32,632952092#u32,243020343#u32,1561436836#u32,1020436789#u32,55227704#u32,1354638029#u32,1231398462#u32,1220349109#u32,1514487249#u32,1716044202#u32,1422215276#u32,1882740077#u32,110355981#u32,222565438#u32,2035926413#u32]
def a4 : State := Array.make 16#usize [2142350296#u32,632952092#u32,243020343#u32,1561437254#u32,1020436789#u32,55227704#u32,1354638029#u32,1231398462#u32,1220349109#u32,1514487249#u32,1716044202#u32,1422215276#u32,1882740077#u32,110355981#u32,222565438#u32,2035926413#u32]
def a5 : State := Array.make 16#usize [2142350296#u32,632952092#u32,243020343#u32,1561437254#u32,1020437224#u32,55227704#u32,1354638029#u32,1231398462#u32,1220349109#u32,1514487249#u32,1716044202#u32,1422215276#u32,1882740077#u32,110355981#u32,222565438#u32,2035926413#u32]
def a6 : State := Array.make 16#usize [2142350296#u32,632952092#u32,243020343#u32,1561437254#u32,1020437224#u32,55228156#u32,1354638029#u32,1231398462#u32,1220349109#u32,1514487249#u32,1716044202#u32,1422215276#u32,1882740077#u32,110355981#u32,222565438#u32,2035926413#u32]
def a7 : State := Array.make 16#usize [2142350296#u32,632952092#u32,243020343#u32,1561437254#u32,1020437224#u32,55228156#u32,1354638498#u32,1231398462#u32,1220349109#u32,1514487249#u32,1716044202#u32,1422215276#u32,1882740077#u32,110355981#u32,222565438#u32,2035926413#u32]
def a8 : State := Array.make 16#usize [2142350296#u32,632952092#u32,243020343#u32,1561437254#u32,1020437224#u32,55228156#u32,1354638498#u32,1231398948#u32,1220349109#u32,1514487249#u32,1716044202#u32,1422215276#u32,1882740077#u32,110355981#u32,222565438#u32,2035926413#u32]
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
  | 0 => PV_RunJoin_ValidatorCell3119.s0
  | 1 => PV_RunJoin_ValidatorCell3119.s3
  | 2 => PV_RunJoin_ValidatorCell3119.s5
  | 3 => PV_RunJoin_ValidatorCell3119.s7
  | 4 => PV_RunJoin_ValidatorCell3119.s9
  | 5 => PV_RunJoin_ValidatorCell3119.s11
  | 6 => PV_RunJoin_ValidatorCell3119.s13
  | 7 => PV_RunJoin_ValidatorCell3119.s15
  | 8 => PV_RunJoin_ValidatorCell3119.s17
  | 9 => PV_RunJoin_ValidatorCell3119.s19
  | 10 => PV_RunJoin_ValidatorCell3119.s21
  | 11 => PV_RunJoin_ValidatorCell3119.s23
  | _ => PV_RunJoin_ValidatorCell3119.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨2142350296#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨632952092#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨243020343#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1561437254#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1020437224#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨55228156#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1354638498#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1231398948#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell3119.s2,PV_RunJoin_ValidatorCell3119.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell3119.s4,PV_RunJoin_ValidatorCell3119.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell3119.s6,PV_RunJoin_ValidatorCell3119.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell3119.s8,PV_RunJoin_ValidatorCell3119.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell3119.s10,PV_RunJoin_ValidatorCell3119.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell3119.s12,PV_RunJoin_ValidatorCell3119.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell3119.s14,PV_RunJoin_ValidatorCell3119.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell3119.s16,PV_RunJoin_ValidatorCell3119.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell3119.s18,PV_RunJoin_ValidatorCell3119.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell3119.s20,PV_RunJoin_ValidatorCell3119.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell3119.s22,PV_RunJoin_ValidatorCell3119.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell3119

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell3219
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [503#u32,520#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [1903829569#u32,618779166#u32,556906812#u32,259396479#u32,539478308#u32,142391747#u32,1992553365#u32,1853663224#u32,1316773122#u32,1614898217#u32,1905284984#u32,1356359869#u32,1790887941#u32,767284748#u32,2017931058#u32,665659179#u32]
def a1 : State := Array.make 16#usize [1903830072#u32,618779166#u32,556906812#u32,259396479#u32,539478308#u32,142391747#u32,1992553365#u32,1853663224#u32,1316773122#u32,1614898217#u32,1905284984#u32,1356359869#u32,1790887941#u32,767284748#u32,2017931058#u32,665659179#u32]
def a2 : State := Array.make 16#usize [1903830072#u32,618779686#u32,556906812#u32,259396479#u32,539478308#u32,142391747#u32,1992553365#u32,1853663224#u32,1316773122#u32,1614898217#u32,1905284984#u32,1356359869#u32,1790887941#u32,767284748#u32,2017931058#u32,665659179#u32]
def a3 : State := Array.make 16#usize [1903830072#u32,618779686#u32,556906812#u32,259396479#u32,539478308#u32,142391747#u32,1992553365#u32,1853663224#u32,1316773122#u32,1614898217#u32,1905284984#u32,1356359869#u32,1790887941#u32,767284748#u32,2017931058#u32,665659179#u32]
def a4 : State := Array.make 16#usize [1903830072#u32,618779686#u32,556906812#u32,259396479#u32,539478308#u32,142391747#u32,1992553365#u32,1853663224#u32,1316773122#u32,1614898217#u32,1905284984#u32,1356359869#u32,1790887941#u32,767284748#u32,2017931058#u32,665659179#u32]
def a5 : State := Array.make 16#usize [1903830072#u32,618779686#u32,556906812#u32,259396479#u32,539478308#u32,142391747#u32,1992553365#u32,1853663224#u32,1316773122#u32,1614898217#u32,1905284984#u32,1356359869#u32,1790887941#u32,767284748#u32,2017931058#u32,665659179#u32]
def a6 : State := Array.make 16#usize [1903830072#u32,618779686#u32,556906812#u32,259396479#u32,539478308#u32,142391747#u32,1992553365#u32,1853663224#u32,1316773122#u32,1614898217#u32,1905284984#u32,1356359869#u32,1790887941#u32,767284748#u32,2017931058#u32,665659179#u32]
def a7 : State := Array.make 16#usize [1903830072#u32,618779686#u32,556906812#u32,259396479#u32,539478308#u32,142391747#u32,1992553365#u32,1853663224#u32,1316773122#u32,1614898217#u32,1905284984#u32,1356359869#u32,1790887941#u32,767284748#u32,2017931058#u32,665659179#u32]
def a8 : State := Array.make 16#usize [1903830072#u32,618779686#u32,556906812#u32,259396479#u32,539478308#u32,142391747#u32,1992553365#u32,1853663224#u32,1316773122#u32,1614898217#u32,1905284984#u32,1356359869#u32,1790887941#u32,767284748#u32,2017931058#u32,665659179#u32]
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
  | 0 => PV_RunJoin_ValidatorCell3219.s0
  | 1 => PV_RunJoin_ValidatorCell3219.s3
  | 2 => PV_RunJoin_ValidatorCell3219.s5
  | 3 => PV_RunJoin_ValidatorCell3219.s7
  | 4 => PV_RunJoin_ValidatorCell3219.s9
  | 5 => PV_RunJoin_ValidatorCell3219.s11
  | 6 => PV_RunJoin_ValidatorCell3219.s13
  | 7 => PV_RunJoin_ValidatorCell3219.s15
  | 8 => PV_RunJoin_ValidatorCell3219.s17
  | 9 => PV_RunJoin_ValidatorCell3219.s19
  | 10 => PV_RunJoin_ValidatorCell3219.s21
  | 11 => PV_RunJoin_ValidatorCell3219.s23
  | _ => PV_RunJoin_ValidatorCell3219.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1903830072#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨618779686#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨556906812#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨259396479#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨539478308#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨142391747#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1992553365#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1853663224#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell3219.s2,PV_RunJoin_ValidatorCell3219.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell3219.s4,PV_RunJoin_ValidatorCell3219.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell3219.s6,PV_RunJoin_ValidatorCell3219.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell3219.s8,PV_RunJoin_ValidatorCell3219.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell3219.s10,PV_RunJoin_ValidatorCell3219.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell3219.s12,PV_RunJoin_ValidatorCell3219.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell3219.s14,PV_RunJoin_ValidatorCell3219.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell3219.s16,PV_RunJoin_ValidatorCell3219.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell3219.s18,PV_RunJoin_ValidatorCell3219.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell3219.s20,PV_RunJoin_ValidatorCell3219.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell3219.s22,PV_RunJoin_ValidatorCell3219.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell3219

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell3319
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [501#u32,518#u32,535#u32,552#u32,569#u32,586#u32,603#u32,620#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a1 : State := Array.make 16#usize [501#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a2 : State := Array.make 16#usize [501#u32,518#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a3 : State := Array.make 16#usize [501#u32,518#u32,535#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a4 : State := Array.make 16#usize [501#u32,518#u32,535#u32,552#u32,0#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a5 : State := Array.make 16#usize [501#u32,518#u32,535#u32,552#u32,569#u32,0#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a6 : State := Array.make 16#usize [501#u32,518#u32,535#u32,552#u32,569#u32,586#u32,0#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a7 : State := Array.make 16#usize [501#u32,518#u32,535#u32,552#u32,569#u32,586#u32,603#u32,0#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a8 : State := Array.make 16#usize [501#u32,518#u32,535#u32,552#u32,569#u32,586#u32,603#u32,620#u32,1095958531#u32,18#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
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
  | 0 => PV_RunJoin_ValidatorCell3319.s0
  | 1 => PV_RunJoin_ValidatorCell3319.s3
  | 2 => PV_RunJoin_ValidatorCell3319.s5
  | 3 => PV_RunJoin_ValidatorCell3319.s7
  | 4 => PV_RunJoin_ValidatorCell3319.s9
  | 5 => PV_RunJoin_ValidatorCell3319.s11
  | 6 => PV_RunJoin_ValidatorCell3319.s13
  | 7 => PV_RunJoin_ValidatorCell3319.s15
  | 8 => PV_RunJoin_ValidatorCell3319.s17
  | 9 => PV_RunJoin_ValidatorCell3319.s19
  | 10 => PV_RunJoin_ValidatorCell3319.s21
  | 11 => PV_RunJoin_ValidatorCell3319.s23
  | _ => PV_RunJoin_ValidatorCell3319.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨501#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨518#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨535#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨552#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨569#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨586#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨603#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨620#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell3319.s2,PV_RunJoin_ValidatorCell3319.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell3319.s4,PV_RunJoin_ValidatorCell3319.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell3319.s6,PV_RunJoin_ValidatorCell3319.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell3319.s8,PV_RunJoin_ValidatorCell3319.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell3319.s10,PV_RunJoin_ValidatorCell3319.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell3319.s12,PV_RunJoin_ValidatorCell3319.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell3319.s14,PV_RunJoin_ValidatorCell3319.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell3319.s16,PV_RunJoin_ValidatorCell3319.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell3319.s18,PV_RunJoin_ValidatorCell3319.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell3319.s20,PV_RunJoin_ValidatorCell3319.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell3319.s22,PV_RunJoin_ValidatorCell3319.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell3319

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell3419
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [400#u32,77#u32,601#u32,618#u32,635#u32,652#u32,669#u32,686#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [820016234#u32,1956929333#u32,1636680544#u32,160014571#u32,2049519928#u32,517510962#u32,7711739#u32,2135764756#u32,1052160426#u32,1760438459#u32,984102268#u32,2100198862#u32,1388088310#u32,2056866746#u32,1028884314#u32,340520453#u32]
def a1 : State := Array.make 16#usize [820016634#u32,1956929333#u32,1636680544#u32,160014571#u32,2049519928#u32,517510962#u32,7711739#u32,2135764756#u32,1052160426#u32,1760438459#u32,984102268#u32,2100198862#u32,1388088310#u32,2056866746#u32,1028884314#u32,340520453#u32]
def a2 : State := Array.make 16#usize [820016634#u32,1956929410#u32,1636680544#u32,160014571#u32,2049519928#u32,517510962#u32,7711739#u32,2135764756#u32,1052160426#u32,1760438459#u32,984102268#u32,2100198862#u32,1388088310#u32,2056866746#u32,1028884314#u32,340520453#u32]
def a3 : State := Array.make 16#usize [820016634#u32,1956929410#u32,1636681145#u32,160014571#u32,2049519928#u32,517510962#u32,7711739#u32,2135764756#u32,1052160426#u32,1760438459#u32,984102268#u32,2100198862#u32,1388088310#u32,2056866746#u32,1028884314#u32,340520453#u32]
def a4 : State := Array.make 16#usize [820016634#u32,1956929410#u32,1636681145#u32,160015189#u32,2049519928#u32,517510962#u32,7711739#u32,2135764756#u32,1052160426#u32,1760438459#u32,984102268#u32,2100198862#u32,1388088310#u32,2056866746#u32,1028884314#u32,340520453#u32]
def a5 : State := Array.make 16#usize [820016634#u32,1956929410#u32,1636681145#u32,160015189#u32,2049520563#u32,517510962#u32,7711739#u32,2135764756#u32,1052160426#u32,1760438459#u32,984102268#u32,2100198862#u32,1388088310#u32,2056866746#u32,1028884314#u32,340520453#u32]
def a6 : State := Array.make 16#usize [820016634#u32,1956929410#u32,1636681145#u32,160015189#u32,2049520563#u32,517511614#u32,7711739#u32,2135764756#u32,1052160426#u32,1760438459#u32,984102268#u32,2100198862#u32,1388088310#u32,2056866746#u32,1028884314#u32,340520453#u32]
def a7 : State := Array.make 16#usize [820016634#u32,1956929410#u32,1636681145#u32,160015189#u32,2049520563#u32,517511614#u32,7712408#u32,2135764756#u32,1052160426#u32,1760438459#u32,984102268#u32,2100198862#u32,1388088310#u32,2056866746#u32,1028884314#u32,340520453#u32]
def a8 : State := Array.make 16#usize [820016634#u32,1956929410#u32,1636681145#u32,160015189#u32,2049520563#u32,517511614#u32,7712408#u32,2135765442#u32,1052160426#u32,1760438459#u32,984102268#u32,2100198862#u32,1388088310#u32,2056866746#u32,1028884314#u32,340520453#u32]
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
  | 0 => PV_RunJoin_ValidatorCell3419.s0
  | 1 => PV_RunJoin_ValidatorCell3419.s3
  | 2 => PV_RunJoin_ValidatorCell3419.s5
  | 3 => PV_RunJoin_ValidatorCell3419.s7
  | 4 => PV_RunJoin_ValidatorCell3419.s9
  | 5 => PV_RunJoin_ValidatorCell3419.s11
  | 6 => PV_RunJoin_ValidatorCell3419.s13
  | 7 => PV_RunJoin_ValidatorCell3419.s15
  | 8 => PV_RunJoin_ValidatorCell3419.s17
  | 9 => PV_RunJoin_ValidatorCell3419.s19
  | 10 => PV_RunJoin_ValidatorCell3419.s21
  | 11 => PV_RunJoin_ValidatorCell3419.s23
  | _ => PV_RunJoin_ValidatorCell3419.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨820016634#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1956929410#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1636681145#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨160015189#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2049520563#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨517511614#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨7712408#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2135765442#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell3419.s2,PV_RunJoin_ValidatorCell3419.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell3419.s4,PV_RunJoin_ValidatorCell3419.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell3419.s6,PV_RunJoin_ValidatorCell3419.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell3419.s8,PV_RunJoin_ValidatorCell3419.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell3419.s10,PV_RunJoin_ValidatorCell3419.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell3419.s12,PV_RunJoin_ValidatorCell3419.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell3419.s14,PV_RunJoin_ValidatorCell3419.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell3419.s16,PV_RunJoin_ValidatorCell3419.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell3419.s18,PV_RunJoin_ValidatorCell3419.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell3419.s20,PV_RunJoin_ValidatorCell3419.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell3419.s22,PV_RunJoin_ValidatorCell3419.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell3419

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell3519
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [703#u32,720#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [610922330#u32,126079099#u32,1982917466#u32,933735870#u32,584773491#u32,1304060905#u32,1184384122#u32,1101204160#u32,1241709131#u32,291159182#u32,1920935269#u32,477452604#u32,517989461#u32,1708406445#u32,652837039#u32,1855831084#u32]
def a1 : State := Array.make 16#usize [610923033#u32,126079099#u32,1982917466#u32,933735870#u32,584773491#u32,1304060905#u32,1184384122#u32,1101204160#u32,1241709131#u32,291159182#u32,1920935269#u32,477452604#u32,517989461#u32,1708406445#u32,652837039#u32,1855831084#u32]
def a2 : State := Array.make 16#usize [610923033#u32,126079819#u32,1982917466#u32,933735870#u32,584773491#u32,1304060905#u32,1184384122#u32,1101204160#u32,1241709131#u32,291159182#u32,1920935269#u32,477452604#u32,517989461#u32,1708406445#u32,652837039#u32,1855831084#u32]
def a3 : State := Array.make 16#usize [610923033#u32,126079819#u32,1982917466#u32,933735870#u32,584773491#u32,1304060905#u32,1184384122#u32,1101204160#u32,1241709131#u32,291159182#u32,1920935269#u32,477452604#u32,517989461#u32,1708406445#u32,652837039#u32,1855831084#u32]
def a4 : State := Array.make 16#usize [610923033#u32,126079819#u32,1982917466#u32,933735870#u32,584773491#u32,1304060905#u32,1184384122#u32,1101204160#u32,1241709131#u32,291159182#u32,1920935269#u32,477452604#u32,517989461#u32,1708406445#u32,652837039#u32,1855831084#u32]
def a5 : State := Array.make 16#usize [610923033#u32,126079819#u32,1982917466#u32,933735870#u32,584773491#u32,1304060905#u32,1184384122#u32,1101204160#u32,1241709131#u32,291159182#u32,1920935269#u32,477452604#u32,517989461#u32,1708406445#u32,652837039#u32,1855831084#u32]
def a6 : State := Array.make 16#usize [610923033#u32,126079819#u32,1982917466#u32,933735870#u32,584773491#u32,1304060905#u32,1184384122#u32,1101204160#u32,1241709131#u32,291159182#u32,1920935269#u32,477452604#u32,517989461#u32,1708406445#u32,652837039#u32,1855831084#u32]
def a7 : State := Array.make 16#usize [610923033#u32,126079819#u32,1982917466#u32,933735870#u32,584773491#u32,1304060905#u32,1184384122#u32,1101204160#u32,1241709131#u32,291159182#u32,1920935269#u32,477452604#u32,517989461#u32,1708406445#u32,652837039#u32,1855831084#u32]
def a8 : State := Array.make 16#usize [610923033#u32,126079819#u32,1982917466#u32,933735870#u32,584773491#u32,1304060905#u32,1184384122#u32,1101204160#u32,1241709131#u32,291159182#u32,1920935269#u32,477452604#u32,517989461#u32,1708406445#u32,652837039#u32,1855831084#u32]
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
  | 0 => PV_RunJoin_ValidatorCell3519.s0
  | 1 => PV_RunJoin_ValidatorCell3519.s3
  | 2 => PV_RunJoin_ValidatorCell3519.s5
  | 3 => PV_RunJoin_ValidatorCell3519.s7
  | 4 => PV_RunJoin_ValidatorCell3519.s9
  | 5 => PV_RunJoin_ValidatorCell3519.s11
  | 6 => PV_RunJoin_ValidatorCell3519.s13
  | 7 => PV_RunJoin_ValidatorCell3519.s15
  | 8 => PV_RunJoin_ValidatorCell3519.s17
  | 9 => PV_RunJoin_ValidatorCell3519.s19
  | 10 => PV_RunJoin_ValidatorCell3519.s21
  | 11 => PV_RunJoin_ValidatorCell3519.s23
  | _ => PV_RunJoin_ValidatorCell3519.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨610923033#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨126079819#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1982917466#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨933735870#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨584773491#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1304060905#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1184384122#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1101204160#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell3519.s2,PV_RunJoin_ValidatorCell3519.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell3519.s4,PV_RunJoin_ValidatorCell3519.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell3519.s6,PV_RunJoin_ValidatorCell3519.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell3519.s8,PV_RunJoin_ValidatorCell3519.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell3519.s10,PV_RunJoin_ValidatorCell3519.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell3519.s12,PV_RunJoin_ValidatorCell3519.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell3519.s14,PV_RunJoin_ValidatorCell3519.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell3519.s16,PV_RunJoin_ValidatorCell3519.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell3519.s18,PV_RunJoin_ValidatorCell3519.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell3519.s20,PV_RunJoin_ValidatorCell3519.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell3519.s22,PV_RunJoin_ValidatorCell3519.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell3519
