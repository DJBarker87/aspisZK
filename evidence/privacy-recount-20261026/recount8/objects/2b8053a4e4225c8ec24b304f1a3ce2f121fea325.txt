import R1Z.ProverRwEntropyObstruction
import R1Z.ProverCommitSemanticTransport26

/-! The obstruction reaches the actual emitted entropy iteration, not merely
an arbitrary function type. Stateful native E1 requires a different interface
or a proved observational transport; a fixed pure dictionary is insufficient
for an unrestricted iteration-by-iteration fixed-tape refinement. -/
set_option autoImplicit false
namespace R1Z.ProverRwEntropyIteration
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open ProverCommitSemanticTransport26
variable [ExternalTypes] [ExternalFuns]
abbrev Secret := aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
abbrev EntropyError := aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError
abbrev Status := core.result.Result Secret EntropyError
abbrev Body := aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body

def outcome : ControlFlow Usize Status → Option Status
  | .cont _ => none
  | .done result => some result


theorem same_iteration_shape (nonce : Array U8 32#usize) (limit first second : Usize)
    (hfirst : first < limit) (hsecond : second < limit) :
    mapR outcome (Body nonce limit first) = mapR outcome (Body nonce limit second) := by
  simp only [Body,
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body,
    hfirst,hsecond,if_true,map_bind]
  repeat' first
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
      try (change (_ × _) at value; rcases value with ⟨value1,value2⟩)
      simp only [Aeneas.Std.uncurry,map_bind,map_if,map_ok,lift,bind_tc_ok,outcome,core.result.Result.Insts.CoreOpsTry.branch]
    | split <;> simp_all only [map_bind,map_if,map_ok,lift,bind_tc_ok,outcome,core.result.Result.Insts.CoreOpsTry.branch]
    | simp only [mapR,outcome,lift,bind_tc_ok,bind_assoc]

theorem no_retry_then_success (nonce : Array U8 32#usize) (limit first second after : Usize)
    (hfirst : first < limit) (hsecond : second < limit) (secret : Secret) :
    ¬ (Body nonce limit first = ok (cont after) ∧
       Body nonce limit second = ok (done (.Ok secret))) := by
  rintro ⟨a,b⟩
  have same := same_iteration_shape nonce limit first second hfirst hsecond
  rw [a,b] at same
  cases same

#print axioms same_iteration_shape
#print axioms no_retry_then_success
end R1Z.ProverRwEntropyIteration
