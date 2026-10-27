-- UNCOMPILED: authoritative library provenance gate; no credit claimed.
-- Private source aggregation of unchanged retained retry/control declarations.
import R1Z.ProverRwFullFuns

-- BEGIN PV_RE_CapValue.lean
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_CapValue
open Aeneas Aeneas.Std Result ProverRwFull

theorem cap_value : prover.ATTEMPT_CAP = 8#usize := by
  unfold prover.ATTEMPT_CAP
  rfl

theorem at_cap : (8#usize) >= prover.ATTEMPT_CAP := by
  rw [cap_value]

theorem below_cap : ¬ (0#usize) >= prover.ATTEMPT_CAP := by
  rw [cap_value]
  change ¬ (8 : Nat) ≤ 0
  exact Nat.not_succ_le_zero 7

#print axioms cap_value
#print axioms at_cap
#print axioms below_cap
end R1Z.PV_RE_CapValue

-- BEGIN PV_RE_RetryStep.lean
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_RetryStep
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Public := aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Compiled := aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
abbrev Secrets := aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
abbrev Store := aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore
abbrev Hash := Slice (Slice U8) → Result (Array U8 32#usize)
abbrev Entropy (C : Type) := core.ops.function.FnMut C Usize (core.result.Result Secrets verifier.Error)
abbrev Reply := Result ((core.result.Result prover.RetriedProof verifier.Error) × Store)

def step
  {T0 : Type}
  (coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst :
  core.ops.function.FnMut T0 Std.Usize (core.result.Result
  aspis_prover.state_only_entropy.StateOnlyAttemptSecrets verifier.Error))
  (next : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore → T0 → Std.Usize →
    Result ((core.result.Result prover.RetriedProof verifier.Error) ×
      aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore))
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (next_attempt : T0) (k : Std.Usize) :
  Result ((core.result.Result prover.RetriedProof verifier.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  := do
  if k >= prover.ATTEMPT_CAP
  then
    ok (core.result.Result.Err verifier.Error.AttemptsExhausted, nonce_store)
  else
    let (r, next_attempt1) ←
      coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst.call_mut
        next_attempt k
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (r1, nonce_store1) ←
        prover.prove_masked_attempt public1 compiled variant hash val
          nonce_store
      match r1 with
      | core.result.Result.Ok p =>
        let (proof, audit) := p
        let i ← Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize)
        ok (core.result.Result.Ok { proof, audit, attempts := i },
          nonce_store1)
      | core.result.Result.Err e =>
        match e with
        | verifier.Error.Parse =>
          ok (core.result.Result.Err verifier.Error.Parse, nonce_store1)
        | verifier.Error.Semantic =>
          ok (core.result.Result.Err verifier.Error.Semantic, nonce_store1)
        | verifier.Error.Transcript =>
          ok (core.result.Result.Err verifier.Error.Transcript, nonce_store1)
        | verifier.Error.Relation =>
          ok (core.result.Result.Err verifier.Error.Relation, nonce_store1)
        | verifier.Error.Merkle =>
          ok (core.result.Result.Err verifier.Error.Merkle, nonce_store1)
        | verifier.Error.Query =>
          ok (core.result.Result.Err verifier.Error.Query, nonce_store1)
        | verifier.Error.Checkpoint =>
          ok (core.result.Result.Err verifier.Error.Checkpoint, nonce_store1)
        | verifier.Error.Allocation =>
          ok (core.result.Result.Err verifier.Error.Allocation, nonce_store1)
        | verifier.Error.Rejected =>
          let i ← Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize)
          next nonce_store1 next_attempt1 i
        | verifier.Error.AttemptsExhausted =>
          ok (core.result.Result.Err verifier.Error.AttemptsExhausted,
            nonce_store1)
        | verifier.Error.Entropy =>
          ok (core.result.Result.Err verifier.Error.Entropy, nonce_store1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          prover.RetriedProof (core.convert.FromSame verifier.Error) residual
      ok (r1, nonce_store)

/-- Complete one-step retry equation, including every continuation and error. -/
theorem unfold_retry {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (v : transport.Variant) (hash : Hash)
    (store : Store) (state : C) (k : Usize) :
    prover.retry_attempt entropy pub compiled v hash store state k =
      step entropy (prover.retry_attempt entropy pub compiled v hash) pub compiled v hash store state k := by
  rw [prover.retry_attempt]
  rfl

#print axioms step
#print axioms unfold_retry
end R1Z.PV_RE_RetryStep

-- BEGIN PV_RE_Increment0.lean
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Increment0
open Aeneas Aeneas.Std Result ProverRwFull

theorem increment : Aeneas.Std.lift (Usize.wrapping_add 0#usize 1#usize) = (Result.ok 1#usize) := by
  apply congrArg Result.ok
  apply (Usize.eq_equiv_bv_eq _ _).mpr
  unfold Usize.wrapping_add UScalar.wrapping_add
  simp only [Usize.ofNat_bv]
  exact BitVec.zero_add _

theorem active : ¬ (0#usize) >= prover.ATTEMPT_CAP := PV_RE_CapValue.below_cap

#print Usize.wrapping_add
#print UScalar.wrapping_add
#print Aeneas.Std.lift
#print core.result.Result.Insts.CoreOpsTry.branch
#print core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
#print axioms increment
#print axioms active
end R1Z.PV_RE_Increment0

-- BEGIN PV_RE_RetryCongruence.lean
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_RetryCongruence
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep
variable [ExternalTypes] [ExternalFuns]

/-- The recursive continuation is consulted only at the incremented counter,
and only after rejection. All entropy and attempt outcomes are retained. -/
theorem congr_at {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (v : transport.Variant) (hash : Hash)
    (store : Store) (state : C) (k j : Usize)
    (f g : Store → C → Usize → Reply)
    (inc : Aeneas.Std.lift (Usize.wrapping_add k 1#usize) = Result.ok j)
    (next : ∀ s c, f s c j = g s c j) :
    step entropy f pub compiled v hash store state k =
      step entropy g pub compiled v hash store state k := by
  unfold step
  split
  · rfl
  · congr 1
    funext x
    rcases x with ⟨r, c⟩
    cases r with
    | Err e => rfl
    | Ok secret =>
      change (prover.prove_masked_attempt pub compiled v hash secret store >>= _) =
        (prover.prove_masked_attempt pub compiled v hash secret store >>= _)
      congr 1
      funext y
      rcases y with ⟨r, s⟩
      cases r with
      | Ok proof => rfl
      | Err e =>
        cases e <;> try rfl
        rw [inc]
        exact next s c

#print axioms congr_at
end R1Z.PV_RE_RetryCongruence

-- BEGIN PV_RE_Increments.lean
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Increments
open Aeneas Aeneas.Std Result ProverRwFull

theorem inc1 : Aeneas.Std.lift (Usize.wrapping_add 1#usize 1#usize) = Result.ok 2#usize := by
  apply congrArg Result.ok
  apply (Usize.eq_equiv_bv_eq _ _).mpr
  unfold Usize.wrapping_add UScalar.wrapping_add
  simp only [Usize.ofNat_bv]
  exact BitVec.ofNat_add_ofNat 1 1

#print axioms inc1

theorem inc2 : Aeneas.Std.lift (Usize.wrapping_add 2#usize 1#usize) = Result.ok 3#usize := by
  apply congrArg Result.ok
  apply (Usize.eq_equiv_bv_eq _ _).mpr
  unfold Usize.wrapping_add UScalar.wrapping_add
  simp only [Usize.ofNat_bv]
  exact BitVec.ofNat_add_ofNat 2 1

#print axioms inc2

theorem inc3 : Aeneas.Std.lift (Usize.wrapping_add 3#usize 1#usize) = Result.ok 4#usize := by
  apply congrArg Result.ok
  apply (Usize.eq_equiv_bv_eq _ _).mpr
  unfold Usize.wrapping_add UScalar.wrapping_add
  simp only [Usize.ofNat_bv]
  exact BitVec.ofNat_add_ofNat 3 1

#print axioms inc3

theorem inc4 : Aeneas.Std.lift (Usize.wrapping_add 4#usize 1#usize) = Result.ok 5#usize := by
  apply congrArg Result.ok
  apply (Usize.eq_equiv_bv_eq _ _).mpr
  unfold Usize.wrapping_add UScalar.wrapping_add
  simp only [Usize.ofNat_bv]
  exact BitVec.ofNat_add_ofNat 4 1

#print axioms inc4

theorem inc5 : Aeneas.Std.lift (Usize.wrapping_add 5#usize 1#usize) = Result.ok 6#usize := by
  apply congrArg Result.ok
  apply (Usize.eq_equiv_bv_eq _ _).mpr
  unfold Usize.wrapping_add UScalar.wrapping_add
  simp only [Usize.ofNat_bv]
  exact BitVec.ofNat_add_ofNat 5 1

#print axioms inc5

theorem inc6 : Aeneas.Std.lift (Usize.wrapping_add 6#usize 1#usize) = Result.ok 7#usize := by
  apply congrArg Result.ok
  apply (Usize.eq_equiv_bv_eq _ _).mpr
  unfold Usize.wrapping_add UScalar.wrapping_add
  simp only [Usize.ofNat_bv]
  exact BitVec.ofNat_add_ofNat 6 1

#print axioms inc6

theorem inc7 : Aeneas.Std.lift (Usize.wrapping_add 7#usize 1#usize) = Result.ok 8#usize := by
  apply congrArg Result.ok
  apply (Usize.eq_equiv_bv_eq _ _).mpr
  unfold Usize.wrapping_add UScalar.wrapping_add
  simp only [Usize.ofNat_bv]
  exact BitVec.ofNat_add_ofNat 7 1

#print axioms inc7
end R1Z.PV_RE_Increments

-- BEGIN PV_RE_FiniteRetry.lean
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_FiniteRetry
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep
variable [ExternalTypes] [ExternalFuns]

/-- Finite iteration of the exact retry step. The terminal is unreachable
before the source cap in the theorem below. No attempt body is evaluated. -/
def runN {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (v : transport.Variant) (hash : Hash) :
    Nat → Store → C → Usize → Reply
  | 0 => fun store _ _ => .ok (.Err .AttemptsExhausted, store)
  | n+1 => step entropy (runN entropy pub compiled v hash n) pub compiled v hash

theorem at8 {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (v : transport.Variant) (hash : Hash)
    (store : Store) (state : C) :
    prover.retry_attempt entropy pub compiled v hash store state 8#usize =
      runN entropy pub compiled v hash 0 store state 8#usize := by
  rw [PV_RE_RetryStep.unfold_retry]
  unfold step
  rw [if_pos PV_RE_CapValue.at_cap]
  rfl

#print axioms runN
#print axioms at8

theorem at7 {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (v : transport.Variant) (hash : Hash)
    (store : Store) (state : C) :
    prover.retry_attempt entropy pub compiled v hash store state 7#usize =
      runN entropy pub compiled v hash 1 store state 7#usize := by
  rw [PV_RE_RetryStep.unfold_retry]
  change step entropy (prover.retry_attempt entropy pub compiled v hash) pub compiled v hash store state 7#usize =
    step entropy (runN entropy pub compiled v hash 0) pub compiled v hash store state 7#usize
  apply PV_RE_RetryCongruence.congr_at entropy pub compiled v hash store state 7#usize 8#usize _ _ PV_RE_Increments.inc7
  intro s c
  exact at8 entropy pub compiled v hash s c

#print axioms at7

theorem at6 {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (v : transport.Variant) (hash : Hash)
    (store : Store) (state : C) :
    prover.retry_attempt entropy pub compiled v hash store state 6#usize =
      runN entropy pub compiled v hash 2 store state 6#usize := by
  rw [PV_RE_RetryStep.unfold_retry]
  change step entropy (prover.retry_attempt entropy pub compiled v hash) pub compiled v hash store state 6#usize =
    step entropy (runN entropy pub compiled v hash 1) pub compiled v hash store state 6#usize
  apply PV_RE_RetryCongruence.congr_at entropy pub compiled v hash store state 6#usize 7#usize _ _ PV_RE_Increments.inc6
  intro s c
  exact at7 entropy pub compiled v hash s c

#print axioms at6

theorem at5 {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (v : transport.Variant) (hash : Hash)
    (store : Store) (state : C) :
    prover.retry_attempt entropy pub compiled v hash store state 5#usize =
      runN entropy pub compiled v hash 3 store state 5#usize := by
  rw [PV_RE_RetryStep.unfold_retry]
  change step entropy (prover.retry_attempt entropy pub compiled v hash) pub compiled v hash store state 5#usize =
    step entropy (runN entropy pub compiled v hash 2) pub compiled v hash store state 5#usize
  apply PV_RE_RetryCongruence.congr_at entropy pub compiled v hash store state 5#usize 6#usize _ _ PV_RE_Increments.inc5
  intro s c
  exact at6 entropy pub compiled v hash s c

#print axioms at5

theorem at4 {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (v : transport.Variant) (hash : Hash)
    (store : Store) (state : C) :
    prover.retry_attempt entropy pub compiled v hash store state 4#usize =
      runN entropy pub compiled v hash 4 store state 4#usize := by
  rw [PV_RE_RetryStep.unfold_retry]
  change step entropy (prover.retry_attempt entropy pub compiled v hash) pub compiled v hash store state 4#usize =
    step entropy (runN entropy pub compiled v hash 3) pub compiled v hash store state 4#usize
  apply PV_RE_RetryCongruence.congr_at entropy pub compiled v hash store state 4#usize 5#usize _ _ PV_RE_Increments.inc4
  intro s c
  exact at5 entropy pub compiled v hash s c

#print axioms at4

theorem at3 {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (v : transport.Variant) (hash : Hash)
    (store : Store) (state : C) :
    prover.retry_attempt entropy pub compiled v hash store state 3#usize =
      runN entropy pub compiled v hash 5 store state 3#usize := by
  rw [PV_RE_RetryStep.unfold_retry]
  change step entropy (prover.retry_attempt entropy pub compiled v hash) pub compiled v hash store state 3#usize =
    step entropy (runN entropy pub compiled v hash 4) pub compiled v hash store state 3#usize
  apply PV_RE_RetryCongruence.congr_at entropy pub compiled v hash store state 3#usize 4#usize _ _ PV_RE_Increments.inc3
  intro s c
  exact at4 entropy pub compiled v hash s c

#print axioms at3

theorem at2 {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (v : transport.Variant) (hash : Hash)
    (store : Store) (state : C) :
    prover.retry_attempt entropy pub compiled v hash store state 2#usize =
      runN entropy pub compiled v hash 6 store state 2#usize := by
  rw [PV_RE_RetryStep.unfold_retry]
  change step entropy (prover.retry_attempt entropy pub compiled v hash) pub compiled v hash store state 2#usize =
    step entropy (runN entropy pub compiled v hash 5) pub compiled v hash store state 2#usize
  apply PV_RE_RetryCongruence.congr_at entropy pub compiled v hash store state 2#usize 3#usize _ _ PV_RE_Increments.inc2
  intro s c
  exact at3 entropy pub compiled v hash s c

#print axioms at2

theorem at1 {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (v : transport.Variant) (hash : Hash)
    (store : Store) (state : C) :
    prover.retry_attempt entropy pub compiled v hash store state 1#usize =
      runN entropy pub compiled v hash 7 store state 1#usize := by
  rw [PV_RE_RetryStep.unfold_retry]
  change step entropy (prover.retry_attempt entropy pub compiled v hash) pub compiled v hash store state 1#usize =
    step entropy (runN entropy pub compiled v hash 6) pub compiled v hash store state 1#usize
  apply PV_RE_RetryCongruence.congr_at entropy pub compiled v hash store state 1#usize 2#usize _ _ PV_RE_Increments.inc1
  intro s c
  exact at2 entropy pub compiled v hash s c

#print axioms at1

theorem at0 {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (v : transport.Variant) (hash : Hash)
    (store : Store) (state : C) :
    prover.retry_attempt entropy pub compiled v hash store state 0#usize =
      runN entropy pub compiled v hash 8 store state 0#usize := by
  rw [PV_RE_RetryStep.unfold_retry]
  change step entropy (prover.retry_attempt entropy pub compiled v hash) pub compiled v hash store state 0#usize =
    step entropy (runN entropy pub compiled v hash 7) pub compiled v hash store state 0#usize
  apply PV_RE_RetryCongruence.congr_at entropy pub compiled v hash store state 0#usize 1#usize _ _ PV_RE_Increment0.increment
  intro s c
  exact at1 entropy pub compiled v hash s c

#print axioms at0
end R1Z.PV_RE_FiniteRetry

-- BEGIN PV_RE_ClientFinite.lean
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ClientFinite
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep
variable [ExternalTypes] [ExternalFuns]

theorem bind_assoc {A B C : Type} (x : Result A)
    (f : A → Result B) (g : B → Result C) :
    ((x >>= f) >>= g) = (x >>= fun a => f a >>= g) := by
  cases x <;> rfl

/-- Complete outer proof-account control equation. The variant callback is
kept as an actual call, including its failures, divergence and both booleans.
The successful branch contains all eight possible retry positions. -/
theorem equation {C : Type}
    (entropy : core.ops.function.FnMut C Usize (Array U8 32#usize))
    (pub : Public) (compiled : Compiled) (hash : Hash) (store : Store) (state : C) :
    RealR1_client.prove_for_proof_accounts entropy pub compiled hash store state =
      (ExternalFuns.op233 .S2 .S2 >>= fun equal =>
        if !equal then .ok (.Err .Semantic, store)
        else PV_RE_FiniteRetry.runN
          (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError entropy)
          pub compiled .S2 hash 8 store state 0#usize) := by
  unfold RealR1_client.prove_for_proof_accounts prover.prove_masked_retrying_with
    core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
    transport.Variant.Insts.CoreCmpPartialEqVariant
  simp only [bind_assoc]
  congr 1
  funext equal
  cases equal with
  | false => rfl
  | true =>
    change (prover.retry_attempt _ pub compiled .S2 hash store state 0#usize >>=
      fun p => .ok (p.1,p.2)) = _
    rw [PV_RE_FiniteRetry.at0]
    cases PV_RE_FiniteRetry.runN
      (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError entropy)
      pub compiled .S2 hash 8 store state 0#usize <;> rfl

#print axioms bind_assoc
#print axioms equation
end R1Z.PV_RE_ClientFinite

-- BEGIN PV_RE_Continue035.lean
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue035
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.prove_masked_attempt`.
Recursive calls remain the original extracted calls. -/
def continueAfter (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (variant : transport.Variant) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (out : Payload (aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      public1)) : Result ((core.result.Result ((alloc.vec.Vec Std.U8) ×
    prover.MaskedFixtureAudit) verifier.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) := do
  let r := out
  let r1 ←
    core.result.Result.map_err
      prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val
    let s1 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ s ]))
    let a ← hash s1
    let a1 ←
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.impl.mask_nonce
        attempt
    let context ←
      aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1
        a a1
    let s2 ←
      Aeneas.Std.lift (Array.to_slice
        (Array.make 30#usize [
          85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8, 58#u8, 82#u8,
          49#u8, 58#u8, 80#u8, 51#u8, 58#u8, 80#u8, 82#u8, 73#u8, 86#u8, 65#u8,
          84#u8, 69#u8, 45#u8, 65#u8, 84#u8, 84#u8, 69#u8, 77#u8, 80#u8, 84#u8
          ]))
    let s3 := alloc.vec.Vec.deref val
    let i ← transport.Variant.tag variant
    let s4 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ i ]))
    let a2 ←
      aspis_core.state_only_hiding.StateOnlyHidingContext.encode context
    let s5 ← Aeneas.Std.lift (Array.to_slice a2)
    let s6 ← Aeneas.Std.lift (Array.to_slice (Array.make 4#usize [ s2, s3, s4, s5 ]))
    let binding ← hash s6
    prover.prove_masked_with_attempt
      aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
      public1 compiled variant hash context binding attempt nonce_store
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((alloc.vec.Vec Std.U8) × prover.MaskedFixtureAudit)
        (core.convert.FromSame verifier.Error) residual
    ok (r2, nonce_store)

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (variant : transport.Variant) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) :
    prover.prove_masked_attempt (public1 := public1) (compiled := compiled) (variant := variant) (hash := hash) (attempt := attempt) (nonce_store := nonce_store) =
      (aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      public1 >>= fun out => continueAfter (public1 := public1) (compiled := compiled) (variant := variant) (hash := hash) (attempt := attempt) (nonce_store := nonce_store) out) := by
  rw [prover.prove_masked_attempt]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (variant : transport.Variant) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (out : Payload (aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      public1))
    (h : (aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      public1) = .ok out) :
    prover.prove_masked_attempt (public1 := public1) (compiled := compiled) (variant := variant) (hash := hash) (attempt := attempt) (nonce_store := nonce_store) = continueAfter (public1 := public1) (compiled := compiled) (variant := variant) (hash := hash) (attempt := attempt) (nonce_store := nonce_store) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (variant : transport.Variant) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (e : Error)
    (h : (aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      public1) = .fail e) :
    prover.prove_masked_attempt (public1 := public1) (compiled := compiled) (variant := variant) (hash := hash) (attempt := attempt) (nonce_store := nonce_store) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (variant : transport.Variant) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
    (h : (aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      public1) = .div) :
    prover.prove_masked_attempt (public1 := public1) (compiled := compiled) (variant := variant) (hash := hash) (attempt := attempt) (nonce_store := nonce_store) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue035

-- BEGIN PV_RE_ContinuationRetry.lean
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ContinuationRetry
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull PV_RE_RetryStep
variable [ExternalTypes] [ExternalFuns]

def stepWithBody
  {T0 : Type}
  (coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst :
  core.ops.function.FnMut T0 Std.Usize (core.result.Result
  aspis_prover.state_only_entropy.StateOnlyAttemptSecrets verifier.Error))
  (attemptBody : Secrets → Store →
    Result ((core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error) × Store))
  (next : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore → T0 → Std.Usize →
    Result ((core.result.Result prover.RetriedProof verifier.Error) ×
      aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore))
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (next_attempt : T0) (k : Std.Usize) :
  Result ((core.result.Result prover.RetriedProof verifier.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  := do
  if k >= prover.ATTEMPT_CAP
  then
    ok (core.result.Result.Err verifier.Error.AttemptsExhausted, nonce_store)
  else
    let (r, next_attempt1) ←
      coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst.call_mut
        next_attempt k
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (r1, nonce_store1) ←
        attemptBody val nonce_store
      match r1 with
      | core.result.Result.Ok p =>
        let (proof, audit) := p
        let i ← Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize)
        ok (core.result.Result.Ok { proof, audit, attempts := i },
          nonce_store1)
      | core.result.Result.Err e =>
        match e with
        | verifier.Error.Parse =>
          ok (core.result.Result.Err verifier.Error.Parse, nonce_store1)
        | verifier.Error.Semantic =>
          ok (core.result.Result.Err verifier.Error.Semantic, nonce_store1)
        | verifier.Error.Transcript =>
          ok (core.result.Result.Err verifier.Error.Transcript, nonce_store1)
        | verifier.Error.Relation =>
          ok (core.result.Result.Err verifier.Error.Relation, nonce_store1)
        | verifier.Error.Merkle =>
          ok (core.result.Result.Err verifier.Error.Merkle, nonce_store1)
        | verifier.Error.Query =>
          ok (core.result.Result.Err verifier.Error.Query, nonce_store1)
        | verifier.Error.Checkpoint =>
          ok (core.result.Result.Err verifier.Error.Checkpoint, nonce_store1)
        | verifier.Error.Allocation =>
          ok (core.result.Result.Err verifier.Error.Allocation, nonce_store1)
        | verifier.Error.Rejected =>
          let i ← Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize)
          next nonce_store1 next_attempt1 i
        | verifier.Error.AttemptsExhausted =>
          ok (core.result.Result.Err verifier.Error.AttemptsExhausted,
            nonce_store1)
        | verifier.Error.Entropy =>
          ok (core.result.Result.Err verifier.Error.Entropy, nonce_store1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          prover.RetriedProof (core.convert.FromSame verifier.Error) residual
      ok (r1, nonce_store)


/-- Actual op226 followed by the named, complete attempt continuation. -/
def attemptCPS (pub : Public) (compiled : Compiled) (v : transport.Variant)
    (hash : Hash) (secret : Secrets) (store : Store) :=
  ExternalFuns.op226 pub >>= fun out => PV_RE_Continue035.continueAfter
    pub compiled v hash secret store out

theorem attempt_eq (pub : Public) (compiled : Compiled) (v : transport.Variant)
    (hash : Hash) (secret : Secrets) (store : Store) :
    prover.prove_masked_attempt pub compiled v hash secret store =
      attemptCPS pub compiled v hash secret store := by
  exact PV_RE_Continue035.equation pub compiled v hash secret store

theorem step_eq {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (v : transport.Variant) (hash : Hash)
    (next : Store → C → Usize → Reply) (store : Store) (state : C) (k : Usize) :
    step entropy next pub compiled v hash store state k =
      stepWithBody entropy (attemptCPS pub compiled v hash) next
        pub compiled v hash store state k := by
  unfold step stepWithBody
  simp only [attempt_eq]
  rfl

/-- Finite retry with the actual source suffix substituted at every attempt. -/
def runCPS {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (v : transport.Variant) (hash : Hash) :
    Nat → Store → C → Usize → Reply
  | 0 => fun store _ _ => .ok (.Err .AttemptsExhausted,store)
  | n+1 => stepWithBody entropy (attemptCPS pub compiled v hash)
      (runCPS entropy pub compiled v hash n) pub compiled v hash

theorem run_eq {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (v : transport.Variant) (hash : Hash)
    (n : Nat) (store : Store) (state : C) (k : Usize) :
    PV_RE_FiniteRetry.runN entropy pub compiled v hash n store state k =
      runCPS entropy pub compiled v hash n store state k := by
  induction n generalizing store state k with
  | zero => rfl
  | succ n ih =>
    change step entropy (PV_RE_FiniteRetry.runN entropy pub compiled v hash n)
      pub compiled v hash store state k = _
    rw [step_eq]
    have hnext : PV_RE_FiniteRetry.runN entropy pub compiled v hash n =
        runCPS entropy pub compiled v hash n := by
      funext s c i
      exact ih s c i
    rw [hnext]
    rfl

theorem whole_client {C : Type}
    (entropy : core.ops.function.FnMut C Usize (Array U8 32#usize))
    (pub : Public) (compiled : Compiled) (hash : Hash) (store : Store) (state : C) :
    RealR1_client.prove_for_proof_accounts entropy pub compiled hash store state =
      (ExternalFuns.op233 .S2 .S2 >>= fun equal =>
        if !equal then .ok (.Err .Semantic,store)
        else runCPS
          (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError entropy)
          pub compiled .S2 hash 8 store state 0#usize) := by
  rw [PV_RE_ClientFinite.equation]
  simp only [run_eq]

#print axioms stepWithBody
#print axioms attemptCPS
#print axioms attempt_eq
#print axioms step_eq
#print axioms runCPS
#print axioms run_eq
#print axioms whole_client
end R1Z.PV_RE_ContinuationRetry

-- BEGIN PV_RE_ShapeControl.lean
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ShapeControl
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep
variable [ExternalTypes] [ExternalFuns]

/-- Exact complete outer control on the transfer constructor. This does not
assert a native fixture association or a dictionary-invocation trace. -/
theorem transfer {C : Type}
    (entropy : core.ops.function.FnMut C Usize (Array U8 32#usize))
    (p : aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (transition : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1)
    (compiled : Compiled) (hash : Hash) (store : Store) (state : C) :
    RealR1_client.prove_for_proof_accounts entropy (.Transfer p transition) compiled hash store state =
      (ExternalFuns.op233 .S2 .S2 >>= fun equal =>
        if !equal then .ok (.Err .Semantic,store)
        else PV_RE_ContinuationRetry.runCPS
          (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError entropy)
          (.Transfer p transition) compiled .S2 hash 8 store state 0#usize) := by
  exact PV_RE_ContinuationRetry.whole_client entropy (.Transfer p transition) compiled hash store state

#print axioms transfer

/-- Exact complete outer control on the withdrawal constructor. This does not
assert a native fixture association or a dictionary-invocation trace. -/
theorem withdrawal {C : Type}
    (entropy : core.ops.function.FnMut C Usize (Array U8 32#usize))
    (p : aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (transition : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1)
    (compiled : Compiled) (hash : Hash) (store : Store) (state : C) :
    RealR1_client.prove_for_proof_accounts entropy (.Withdrawal p transition) compiled hash store state =
      (ExternalFuns.op233 .S2 .S2 >>= fun equal =>
        if !equal then .ok (.Err .Semantic,store)
        else PV_RE_ContinuationRetry.runCPS
          (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError entropy)
          (.Withdrawal p transition) compiled .S2 hash 8 store state 0#usize) := by
  exact PV_RE_ContinuationRetry.whole_client entropy (.Withdrawal p transition) compiled hash store state

#print axioms withdrawal
end R1Z.PV_RE_ShapeControl
