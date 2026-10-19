import Aeneas
set_option autoImplicit false
namespace AspisR1.RuntimeMeterCallBound
/-- Costs already successfully debited. A start may fail later without
returning a digest, so charging starts conservatively bounds completions. -/
structure Charge where
  units : Nat
  digestStarts : Nat

def starts : List Charge → Nat
  | [] => 0
  | x :: xs => x.digestStarts + starts xs

/-- Runtime refinement must justify these transitions and match each digest
to a distinct paid start. This definition does not assume a query-count cap. -/
inductive MeteredPrefix (minCost : Nat) : Nat → List Charge → Nat → Prop
  | nil (remaining : Nat) : MeteredPrefix minCost remaining [] remaining
  | step {before remaining : Nat} {event : Charge} {rest : List Charge}
      (paid : event.units ≤ before)
      (covered : minCost * event.digestStarts ≤ event.units)
      (tail : MeteredPrefix minCost (before - event.units) rest remaining) :
      MeteredPrefix minCost before (event :: rest) remaining

theorem remaining_add_cost_le {c before remaining : Nat} {events : List Charge}
    (h : MeteredPrefix c before events remaining) :
    remaining + c * starts events ≤ before := by
  induction h with
  | nil r => simp [starts]
  | @step before remaining event rest paid covered tail ih =>
    simp only [starts, Nat.mul_add]
    omega

theorem paid_starts_bound {c before remaining : Nat} {events : List Charge}
    (h : MeteredPrefix c before events remaining) : c * starts events ≤ before := by
  have hb := remaining_add_cost_le h
  omega

/-- Any trace cardinality injectively charged to starts is covered, including
traces ending in rejection, panic, compute exhaustion, or account failure. -/
theorem counted_calls_bound {c before remaining calls : Nat} {events : List Charge}
    (h : MeteredPrefix c before events remaining) (matched : calls ≤ starts events) :
    c * calls ≤ before := by
  exact Nat.le_trans (Nat.mul_le_mul_left c matched) (paid_starts_bound h)

def transactionCap : Nat := 1400000
def hashBaseCost : Nat := 85
def perTransactionCap : Nat := 16470
def twoTransactionCap : Nat := 32940

theorem per_transaction {before remaining calls : Nat} {events : List Charge}
    (h : MeteredPrefix hashBaseCost before events remaining)
    (budget : before ≤ transactionCap) (matched : calls ≤ starts events) :
    calls ≤ perTransactionCap := by
  have hc := counted_calls_bound h matched
  simp only [hashBaseCost, transactionCap, perTransactionCap] at *
  omega

theorem two_transactions {b1 b2 r1 r2 q1 q2 : Nat} {e1 e2 : List Charge}
    (h1 : MeteredPrefix hashBaseCost b1 e1 r1)
    (h2 : MeteredPrefix hashBaseCost b2 e2 r2)
    (cap1 : b1 ≤ transactionCap) (cap2 : b2 ≤ transactionCap)
    (match1 : q1 ≤ starts e1) (match2 : q2 ≤ starts e2) :
    q1 + q2 ≤ twoTransactionCap := by
  have hc1 := per_transaction h1 cap1 match1
  have hc2 := per_transaction h2 cap2 match2
  simp only [perTransactionCap, twoTransactionCap] at *
  omega
#print axioms remaining_add_cost_le
#print axioms paid_starts_bound
#print axioms counted_calls_bound
#print axioms per_transaction
#print axioms two_transactions
end AspisR1.RuntimeMeterCallBound
