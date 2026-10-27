import R1Z.PV_RE_Increments
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
