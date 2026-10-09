import SameBodyCompactTerminal

/-! DRAFT: causal compact-tail translation and an executed terminal check.
The reply tree is translated uniformly, not obtained from a finished body.
The word is serialized from that tree only on the realised continuation.
The scalar input and post-query weight are explicit boundaries: this file
does not assert that Rust, the ordinary/image producer, or authenticated
openings have constructed them. The earlier opened-covector theorem supplies
their query-discrepancy connection separately. No new acceptance rule is
proposed; `check` is the field-level dot/compact-scalar comparison.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
namespace AspisV8Completion.SameBodyTerminalExecution
open SameBodyRelation SameBodyQueryClaimExact SameBodyCompactTerminal
open AspisV8.OptimizedRelationRefinement AspisV8.TypedRelationTerminal
open AspisV5FriRelationCandidateBridge
open scoped BigOperators
variable {K : Type*} [Field K] [DecidableEq K]
variable {Schedule : Type*}
noncomputable section

def first (t : Tail K 3) : SameBodyRelation.Sent K :=
  match t with | .round m _ => m

def second (t : Tail K 3) (a1 : K) : SameBodyRelation.Sent K :=
  match t with | .round _ next => match next a1 with | .round m _ => m

def third (t : Tail K 3) (a1 a2 : K) : SameBodyRelation.Sent K :=
  match t with
  | .round _ next => match next a1 with
    | .round _ next2 => match next2 a2 with | .round m _ => m

/-- The first message does not read a challenge; second reads only a1;
third reads a1,a2. There is no completed-word or future-alpha argument. -/
def typedTail (t : Tail K 3) : TailFields (K := K) where
  first := parts (first t)
  second := fun a1 => parts (second t a1)
  third := fun a1 a2 => parts (third t a1 a2)

theorem causal_tail_claim (quarter initial : K) (t : Tail K 3)
    (coins : Fin 3 → K) :
    tailClaim (ringArithmetic quarter).toArithmetic t coins initial =
      sourceHorner quarter
        (sourceHorner quarter
          (sourceHorner quarter initial (typedTail t).first (coins 0))
          ((typedTail t).second (coins 0)) (coins 1))
        ((typedTail t).third (coins 0) (coins 1)) (coins 2) := by
  cases t with
  | round m1 n1 =>
    generalize h1 : n1 (coins 0) = t1
    cases t1 with
    | round m2 n2 =>
      generalize h2 : n2 (coins 1) = t2
      cases t2 with
      | round m3 n3 =>
        have h3 : n3 (coins 2) = Tail.done := by cases n3 (coins 2); rfl
        have index1 : (0 : Fin 2).succ = (1 : Fin 3) := rfl
        have index2 : (0 : Fin 1).succ.succ = (2 : Fin 3) := rfl
        simp only [tailClaim, typedTail, first, second, third,
          index1, index2, h1, h2, h3]
        rw [compact_to_sourceHorner, compact_to_sourceHorner, compact_to_sourceHorner]

/-- A separately executed scalar computation and folded terminal dot.
All final and response fields are projected from the one word. -/
def check (quarter : K) (word : Word K) (weight : Fin 256 → K)
    (initial : K) (coins : Fin 3 → K) : Bool :=
  decide (candidateClaim (tailDual weight (coins 0) (coins 1) (coins 2))
    (tailPrimal (finalValues word) (coins 0) (coins 1) (coins 2)) =
      SameBodyQueryClaim.terminalClaim (ringArithmetic quarter) word coins initial)

/-- This is not a reconstruction of an adversary from a finished proof.
The same legal reply tree supplies every continuation on both sides. -/
theorem produced_check_iff_raw_acceptance (quarter initial : K)
    (early : Fin 417 → K) (strategy : SameBodyRelation.Strategy K Schedule)
    (tau alpha0 rho : K) (queries : Schedule) (coins : Fin 3 → K)
    (weight : Fin 256 → K) :
    check quarter (produce early strategy tau alpha0 queries rho coins)
      weight initial coins = true ↔
    (typedTail (((strategy tau).afterAlpha0 alpha0).afterQueries queries rho)).raw.accepts
      quarter weight ((strategy tau).afterAlpha0 alpha0).final256 initial
      [coins 0, coins 1, coins 2] := by
  have scalar := SameBodyQueryClaim.produced_terminal (ringArithmetic quarter)
    early strategy tau alpha0 rho queries coins initial
  rw [causal_tail_claim] at scalar
  have final : finalValues (produce early strategy tau alpha0 queries rho coins) =
      ((strategy tau).afterAlpha0 alpha0).final256 := by
    unfold produce
    exact assembled_final _ _ _
  simp only [check, decide_eq_true_eq, final, scalar]
  simp only [TailFields.raw, RawRounds.accepts, nextClaim_source_horner,
    tailDual, tailPrimal]

/-- An actual true result of the independent terminal comparison constructs
the existing discrepancy game's terminal-zero event. There is no terminal
equality, game acceptance, image validity, or decoder success premise. -/
theorem produced_check_constructs_terminal_zero (quarter initial : K)
    (hq : quarter * 4 = 1)
    (early : Fin 417 → K) (strategy : SameBodyRelation.Strategy K Schedule)
    (tau alpha0 rho : K) (queries : Schedule) (coins : Fin 3 → K)
    (weight : Fin 256 → K)
    (success : check quarter (produce early strategy tau alpha0 queries rho coins)
      weight initial coins = true) :
    terminalZero
      ((typedTail (((strategy tau).afterAlpha0 alpha0).afterQueries queries rho)).raw.toGame
        quarter hq weight ((strategy tau).afterAlpha0 alpha0).final256 initial)
      [coins 0, coins 1, coins 2] := by
  apply (raw_acceptance_iff_terminal_zero quarter hq _ _ _ _ _).mp
  exact (produced_check_iff_raw_acceptance quarter initial early strategy tau alpha0 rho
    queries coins weight).mp success

#print produced_check_constructs_terminal_zero
#print axioms causal_tail_claim
#print axioms produced_check_iff_raw_acceptance
#print axioms produced_check_constructs_terminal_zero
end
end AspisV8Completion.SameBodyTerminalExecution
