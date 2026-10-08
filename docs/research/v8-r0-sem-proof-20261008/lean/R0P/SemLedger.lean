import Mathlib.Tactic

/-! Lead: the pair-forest SEM error ledger (numerics only).

Mirrors `AspisFormal.Pool.V7K15FailureRootInventory` for the pair-forest
semantic phase. Each branch's numerator is the number of bad challenge values
for one fixed trace; branches whose bad set depends on the candidate trace
are unioned over the at most 100 candidates of `R0.ListsResponses.Lambda`
(`Lambda_card`), since every semantic challenge precedes the opening layer
that selects the candidate.

Sources for the counts: 29 θ-lanes (pair_forest_semantic_terminal.rs:67),
1024 rows and per-round degree 27 (:45–46), 136 links with at most 272
enabled endpoints (C:27–164, G5), μ batching of two helper sums
(:1307–1308), zerocheck over 10 coordinates. The per-branch bad-set
theorems are the G6/G7/G10 obligations; this file fixes the ledger. -/
set_option autoImplicit false
namespace R0P.SemLedger

inductive Branch
  | tupleCompression   -- λ: a nonzero coefficient of Π(X−c_p(λ)) − Π(X−c_c(λ)), degree ≤ 16·136
  | activePole         -- χ equals an enabled compressed endpoint value, or χ = 0 (empty slots)
  | copyChi            -- χ is a root of the nonzero partial-fraction numerator, degree ≤ 271
  | muBatch            -- μ is a root of the nonzero degree-2 batching polynomial
  | thetaLane          -- θ is a root of a nonzero 29-lane row composition, degree ≤ 28
  | zerocheckPoint     -- zc is a zero of the nonzero multilinear extension, 10 variables
  | sumcheckRounds     -- one of 10 rounds, each a nonzero degree-27 difference
  deriving DecidableEq, Repr

def branches : List Branch :=
  [.tupleCompression, .activePole, .copyChi, .muBatch, .thetaLane, .zerocheckPoint, .sumcheckRounds]

/-- Bad values for one fixed trace. -/
def singleTraceCap : Branch → Nat
  | .tupleCompression => 16 * 136
  | .activePole => 273
  | .copyChi => 271
  | .muBatch => 2
  | .thetaLane => 28
  | .zerocheckPoint => 10
  | .sumcheckRounds => 10 * 27

/-- Every branch depends on the candidate trace, so each is charged ×100. -/
def causalCap (b : Branch) : Nat := 100 * singleTraceCap b

theorem singleTrace_sum : (branches.map singleTraceCap).sum = 3030 := by decide

theorem causal_sum : (branches.map causalCap).sum = 303000 := by decide

def P : Nat := 2 ^ 31 - 1

/-- The pair-forest SEM mass is below `2^-105` over `|QM31| − 1`. -/
theorem causal_le_two_pow_neg_105 :
    (303000 : ℚ) / ((P ^ 4 - 1 : Nat) : ℚ) ≤ 1 / 2 ^ 105 := by
  norm_num [P]

/-- It is also below the V7 K1.5 figure 396430, so the existing ledger's
reporting bounds remain valid for this circuit. -/
theorem causal_le_v7 : 303000 ≤ 396430 := by decide

#print axioms singleTrace_sum
#print axioms causal_sum
#print axioms causal_le_two_pow_neg_105
#print axioms causal_le_v7
end R0P.SemLedger
