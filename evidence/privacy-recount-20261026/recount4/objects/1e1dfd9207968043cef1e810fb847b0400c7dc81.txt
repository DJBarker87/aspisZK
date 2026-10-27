import R1Z.ProverRwFullFuns
import R1Z.ProverCommitRetrySource34
import R1Z.ProverCommitSemanticTransport26

/-! Retry control for the actual rewritten emission. The per-attempt body is
still the actual source function, with its explicit external dictionary;
no body/model or entropy-distribution equation is assumed here. -/
set_option autoImplicit false
namespace R1Z.ProverRwRetryModel
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitSemanticTransport26
variable [ExternalTypes] [ExternalFuns]
abbrev Store := aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore
abbrev Secret := aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
abbrev Proof := alloc.vec.Vec U8 × prover.MaskedFixtureAudit
abbrev Pub := aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Compiled := aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
abbrev Hash := Slice (Slice U8) → Result (Array U8 32#usize)
abbrev Entropy (C : Type) := core.ops.function.FnMut C Usize (core.result.Result Secret verifier.Error)

def error : verifier.Error → ProverCommitRetry34.Error
  | .Parse => .Parse
  | .Semantic => .Semantic
  | .Transcript => .Transcript
  | .Relation => .Relation
  | .Merkle => .Merkle
  | .Query => .Query
  | .Checkpoint => .Checkpoint
  | .Allocation => .Allocation
  | .Rejected => .Rejected
  | .AttemptsExhausted => .AttemptsExhausted
  | .Entropy => .Entropy

def sourceOutput (v : core.result.Result prover.RetriedProof verifier.Error × Store) :
    ProverCommitRetry34.Step (ProverCommitRetry34.Published Proof) × Store :=
  (match v.1 with
    | .Ok p => .done ⟨(p.proof,p.audit),p.attempts.val⟩
    | .Err e => .stop (error e), v.2)

def drop {C : Type} (v : ProverCommitRetry34.Step (ProverCommitRetry34.Published Proof) × (C × Store)) :=
  (v.1,v.2.2)

def attempt {C : Type} (entropy : Entropy C) (pub : Pub) (compiled : Compiled)
    (variant : transport.Variant) (hash : Hash) : ProverCommitRetry34.Attempt (C × Store) Proof :=
  fun k s => do
    let (r,after) ← entropy.call_mut s.1 (ProverCommitRetrySource34.word k)
    match r with
    | .Err e => ok (.stop (error e),(after,s.2))
    | .Ok secret =>
      let (r1,store) ← prover.prove_masked_attempt pub compiled variant hash secret s.2
      match r1 with
      | .Ok p => ok (.done p,(after,store))
      | .Err .Rejected => ok (.retry,(after,store))
      | .Err e => ok (.stop (error e),(after,store))

theorem retry {C : Type} (entropy : Entropy C) (pub : Pub) (compiled : Compiled)
    (variant : transport.Variant) (hash : Hash) (store : Store) (callback : C)
    (k : Usize) (n : Nat) (bound : k.val+n=8) :
    mapR sourceOutput (prover.retry_attempt entropy pub compiled variant hash store callback k) =
      mapR drop (ProverCommitRetry34.run (attempt entropy pub compiled variant hash) n k.val (callback,store)) := by
  induction n generalizing store callback k with
  | zero =>
    have cap : k >= prover.ATTEMPT_CAP := by
      simp only [prover.ATTEMPT_CAP]
      change 8 ≤ k.val
      omega
    rw [prover.retry_attempt]
    simp only [cap,if_true,ProverCommitRetry34.run,map_ok,sourceOutput,error,drop]
  | succ n ih =>
    have below : ¬ k >= prover.ATTEMPT_CAP := by
      simp only [prover.ATTEMPT_CAP]
      change ¬ 8 ≤ k.val
      omega
    have add := ProverCommitRetrySource34.add_one k (by omega)
    have next : (Usize.wrapping_add k 1#usize).val+n=8 := by omega
    rw [prover.retry_attempt]
    simp only [below,if_false,ProverCommitRetry34.run,attempt,
      ProverCommitRetrySource34.word_val,map_bind]
    cases ent : entropy.call_mut callback k with
    | fail e => rfl
    | div => rfl
    | ok out =>
      rcases out with ⟨status,after⟩
      cases status with
      | Err e =>
        cases e <;> simp only [ent,bind_tc_ok,Aeneas.Std.uncurry,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from,ProverCommitRetry34.run,map_ok,drop,sourceOutput,error]
      | Ok secret =>
        simp only [ent,bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch]
        cases body : prover.prove_masked_attempt pub compiled variant hash secret store with
        | fail e => rfl
        | div => rfl
        | ok out =>
          rcases out with ⟨status,afterStore⟩
          cases status with
          | Ok p =>
            rcases p with ⟨proof,audit⟩
            simp only [body,bind_tc_ok,Aeneas.Std.uncurry,map_ok,sourceOutput,drop,add,lift,bind_tc_ok,map_ok]
          | Err e =>
            cases e <;> simp only [body,bind_tc_ok,Aeneas.Std.uncurry,map_ok,sourceOutput,drop,error,lift,bind_tc_ok]
            simpa only [add] using ih afterStore after (Usize.wrapping_add k 1#usize) next

#print axioms retry
end R1Z.ProverRwRetryModel
