import PV_EVH_NonzeroStep
import PV_EVH_PrefixLoop
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NonzeroFlow
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]
/-- Interpret the actual source loop instead of answering the whole helper.
The checked primitive/runtime fidelity and panic-free domain still need audit. -/
def loop (fuel : Nat) (bytes : Array U8 32#usize) (combined : U8) (i : Usize) : P U8 :=
  PV_EVH_PrefixLoop.loop
    (fun (combined, i) => PV_EVH_NonzeroStep.run bytes combined i {}) fuel (combined, i)

theorem loop_fixed (fuel : Nat) (bytes : Array U8 32#usize) (combined : U8) (i : Usize) :
    FinishedView (loop fuel bytes combined i)
      (aspis_prover.state_only_entropy.entropy_nonzero32_loop bytes combined i) := by
  apply PV_EVH_PrefixLoop.fixed_recursive
    (fun (combined, i) => PV_EVH_NonzeroStep.run bytes combined i {})
    (fun (combined, i) => aspis_prover.state_only_entropy.entropy_nonzero32_loop.body bytes combined i)
    (fun (combined, i) => aspis_prover.state_only_entropy.entropy_nonzero32_loop bytes combined i)
  · rintro ⟨combined, i⟩
    unfold aspis_prover.state_only_entropy.entropy_nonzero32_loop
    rw [Aeneas.Std.loop.eq_def]
    cases h : aspis_prover.state_only_entropy.entropy_nonzero32_loop.body bytes combined i with
    | ok cf => cases cf <;> rfl
    | fail e => rfl
    | div => rfl
  · rintro ⟨combined, i⟩
    exact PV_EVH_NonzeroStep.run_fixed bytes combined i {} {}

def run (fuel : Nat) (bytes : Array U8 32#usize) : P Bool := do
  let combined ← loop fuel bytes 0#u8 0#usize
  pure (combined != 0#u8)

theorem run_fixed (fuel : Nat) (bytes : Array U8 32#usize) :
    FinishedView (run fuel bytes) (aspis_prover.state_only_entropy.entropy_nonzero32 bytes) := by
  unfold run aspis_prover.state_only_entropy.entropy_nonzero32
  apply PV_EVH_Prefix.bind_fixed
  · exact loop_fixed fuel bytes _ _
  · intro combined
    exact PV_EVH_Prefix.lift_fixed _
#print axioms loop_fixed
#print axioms run_fixed
end PV_EVH_NonzeroFlow
