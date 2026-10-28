import R1Z.PV_RDB2C_PV_B2_F_FrozenCell
import R1Z.PV_RDB2C_PV_B2_F_AllocationTransport
set_option autoImplicit false
namespace PV_B2_F_MaterializeFrozen
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_MutationStep
abbrev Outcome := PV_B2_F_AllocationTransport.Outcome
/-- Full state restoration with the frozen raw match and ordered factor folds. -/
def remaining (w : host_weights.Weights) (k : Powers) : Nat → Usize → Out → Result Out
  | 0, _, out => ok out
  | n+1, j, out => do
    let initial ← Array.index_usize out j
    let x ← PV_B2_F_FrozenCell.original w k j initial
    let out1 ← Array.update out j x
    remaining w k n (Usize.wrapping_add j 1#usize) out1

theorem loops (w : host_weights.Weights) (k : Powers) (n : Nat) (j : Usize) (out : Out) :
    PV_B2_F_OriginalMutation.remaining w k n j out = remaining w k n j out := by
  induction n generalizing j out with
  | zero => rfl
  | succ n ih =>
    simp only [PV_B2_F_OriginalMutation.remaining,remaining,PV_B2_F_FrozenCell.source,ih]

def original (event : Outcome) (w : host_weights.Weights) (kappa : E) :
    Result PV_B2_F_AllocationTransport.RustResult :=
  match event with
  | .denied => ok (.Err verifier.Error.Allocation)
  | .supplied => do
    let k ← host_weights.powers7 kappa
    let out ← remaining w k 1024 0#usize PV_B2_F_AllocationTransport.zeros
    ok (.Ok out)

theorem originals (event : Outcome) (w : host_weights.Weights) (kappa : E) :
    PV_B2_F_AllocationTransport.original event w kappa = original event w kappa := by
  cases event <;> simp only [PV_B2_F_AllocationTransport.original,original,loops]

theorem complete_result (event : Outcome) (w : host_weights.Weights) (kappa : E) :
    PV_B2_F_AllocationTransport.copied event w kappa = original event w kappa :=
  (PV_B2_F_AllocationTransport.equal event w kappa).trans (originals event w kappa)
#print axioms loops
#print axioms originals
#print axioms complete_result
end PV_B2_F_MaterializeFrozen
