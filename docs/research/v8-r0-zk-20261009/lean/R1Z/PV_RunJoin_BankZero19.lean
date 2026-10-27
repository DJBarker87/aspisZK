import R1Z.PV_RunJoin_BankCertificate19
import R1Z.PV_RunJoin_ValidatorZero19
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BankZero19
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorZero19.s0
  | 1 => PV_RunJoin_ValidatorZero19.s3
  | 2 => PV_RunJoin_ValidatorZero19.s5
  | 3 => PV_RunJoin_ValidatorZero19.s7
  | 4 => PV_RunJoin_ValidatorZero19.s9
  | 5 => PV_RunJoin_ValidatorZero19.s11
  | 6 => PV_RunJoin_ValidatorZero19.s13
  | 7 => PV_RunJoin_ValidatorZero19.s15
  | 8 => PV_RunJoin_ValidatorZero19.s17
  | 9 => PV_RunJoin_ValidatorZero19.s19
  | 10 => PV_RunJoin_ValidatorZero19.s21
  | 11 => PV_RunJoin_ValidatorZero19.s23
  | _ => PV_RunJoin_ValidatorZero19.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add PV_RunJoin_ValidatorZero19.s0.val[lane.val]!
      PV_RunJoin_ValidatorZero19.s0.val[lane.val]! = ok sum ∧
    PV_RunJoin_ValidatorZero19.s0.set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = PV_RunJoin_ValidatorZero19.s0 := by
  intro lane
  fin_cases lane <;> exact ⟨0#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add

theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorZero19.s2,PV_RunJoin_ValidatorZero19.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorZero19.s4,PV_RunJoin_ValidatorZero19.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorZero19.s6,PV_RunJoin_ValidatorZero19.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorZero19.s8,PV_RunJoin_ValidatorZero19.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorZero19.s10,PV_RunJoin_ValidatorZero19.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorZero19.s12,PV_RunJoin_ValidatorZero19.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorZero19.s14,PV_RunJoin_ValidatorZero19.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorZero19.s16,PV_RunJoin_ValidatorZero19.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorZero19.s18,PV_RunJoin_ValidatorZero19.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorZero19.s20,PV_RunJoin_ValidatorZero19.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorZero19.s22,PV_RunJoin_ValidatorZero19.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := PV_RunJoin_ValidatorZero19.s0, absorption := PV_RunJoin_ValidatorZero19.s0,
  absorbed := fun _ => PV_RunJoin_ValidatorZero19.s0, states := states,
  before := rfl, after := rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankZero19
