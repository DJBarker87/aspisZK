import R1Z.PV_RunJoin_SaltStepSize64
import R1Z.PV_RunJoin_QueryLeafVisit64
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SaltLoopSize64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ExternalFuns]
abbrev Salts := alloc.vec.Vec (Array U8 32#usize)

def Size (total pending : Nat) : core.result.Result Salts verifier.Error → Prop
  | .Err _ => True
  | .Ok salts => salts.length+pending=total

theorem complete (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (hash : aspis_core.digest.LegacyHashFn) (tag : U8) (count : Usize) (small : count.val≤262144)
    (n total : Nat) (result : core.result.Result Salts verifier.Error) (i : Usize)
    (rank : i.val+n=count.val) (size : Size total n result) :
    Post (Size total 0) (prover.derive_private_salts_loop reserved context hash tag count result i) := by
  induction n generalizing result i with
  | zero =>
    have stop : ¬i<count := by change ¬i.val<count.val;omega
    unfold prover.derive_private_salts_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [prover.derive_private_salts_loop.body,stop,if_false,bind_tc_ok]
    exact size
  | succ n ih =>
    have more : i<count := by change i.val<count.val;omega
    have inc := PV_RunJoin_QueryLeafVisit64.increment i (by change i.val<count.val at more;omega)
    unfold prover.derive_private_salts_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [prover.derive_private_salts_loop.body,more,if_true,lift,bind_tc_ok,bind_assoc_eq]
    cases result with
    | Err e =>
      simp only [bind_tc_ok]
      exact ih (.Err e) (Usize.wrapping_add i 1#usize) (by rw [inc];omega) trivial
    | Ok salts =>
      apply PV_RunJoin_PostBind63.guarded _ _ _ _
        (PV_RunJoin_SaltStepSize64.step reserved context hash tag (UScalar.cast .U32 i) salts)
      intro status hstatus
      apply ih status (Usize.wrapping_add i 1#usize) (by rw [inc];omega)
      cases status with
      | Err e => trivial
      | Ok next =>
        change salts.length+(n+1)=total at size
        change next.length=salts.length+1 at hstatus
        change next.length+n=total
        omega

#print axioms Size
#print axioms complete
end R1Z.PV_RunJoin_SaltLoopSize64
