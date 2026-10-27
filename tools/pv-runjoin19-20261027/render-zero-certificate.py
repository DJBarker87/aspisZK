from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s='''import R1Z.PV_RunJoin_BankCertificate19
import R1Z.PV_RunJoin_ValidatorZero19
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BankZero19
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
'''
s+='def states (n : Nat) : State := match n with\n  | 0 => PV_RunJoin_ValidatorZero19.s0\n'+''.join(f'  | {n} => PV_RunJoin_ValidatorZero19.s{2*n+1}\n' for n in range(1,12))+'  | _ => PV_RunJoin_ValidatorZero19.s0\n'
s+='''theorem add : ∀ lane : Fin 8, ∃ sum,
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
'''
s+=''.join(f'  · exact ⟨PV_RunJoin_ValidatorZero19.s{2*n+2},PV_RunJoin_ValidatorZero19.pair{n}⟩\n' for n in range(11))
s+='''#print axioms pairs
def certificate : Certificate := {
  pre := PV_RunJoin_ValidatorZero19.s0, absorption := PV_RunJoin_ValidatorZero19.s0,
  absorbed := fun _ => PV_RunJoin_ValidatorZero19.s0, states := states,
  before := rfl, after := rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankZero19
''';(L/'PV_RunJoin_BankZero19.lean').write_text(s)
