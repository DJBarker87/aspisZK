import R1Z.QueryScanFreshProgram
import R1Z.ProverCommitFuelMass22
/-! Adaptive fuel-window probability in one memoized shared oracle. There
is no conditioning on an independently postulated random start. Freshness
is measured by the compiled execution itself, including earlier unmarked
reads and repeated-address caching. Source caller reachability is separate. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitAdaptiveFuel23
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
open AspisV8R19.MemoizedProgramLaw R1Z.QueryScanFreshProgram
open ProverCommitFuelMass22
attribute [local instance] Classical.propDecidable
variable {Address Answer : Type} [DecidableEq Address]

def markedFailure (zero : Answer) (program : Marked Address Answer k)
    (table : Address → Answer) : Prop :=
  let result := (eval table (compile program ∅ id)).2
  result.1 = true ∧ exhausted zero result.2

/-- Addresses of the five marked draws may depend on every earlier answer.
Only paths on which all marked addresses are fresh are charged here. -/
theorem adaptive_exhaustion [Fintype Address] [Fintype Answer] [Nonempty Answer]
    (zero : Answer) (program : Marked Address Answer k) :
    eventMass (markedFailure zero program) ≤ 1 / (Fintype.card Answer : ℚ)^k := by
  have bound := fresh_oracle_bound program (exhausted zero)
  rw [exhaustion_mass] at bound
  unfold eventMass
  convert bound using 1 <;>
    congr 1 <;> funext table <;> dsimp only [markedFailure] <;> split_ifs <;> rfl

/-- The same bound for arbitrary source failure predicates that imply the
fresh, all-zero marked event. The containment is a visible source obligation. -/
theorem source_exhaustion [Fintype Address] [Fintype Answer] [Nonempty Answer]
    (zero : Answer) (program : Marked Address Answer k)
    (failure : (Address → Answer) → Prop)
    (source_event : ∀ table, failure table → markedFailure zero program table) :
    eventMass failure ≤ 1 / (Fintype.card Answer : ℚ)^k :=
  (eventMass_mono _ _ source_event).trans (adaptive_exhaustion zero program)

/-- Twenty-four possibly dependent, adaptive search instances in one shared
oracle; no inter-instance independence and no fixed-start marginal argument. -/
theorem adaptive_union [Fintype Address] [Fintype Answer] [Nonempty Answer]
    (zero : Answer) (program : Fin count → Marked Address Answer k)
    (cardinality : p ≤ Fintype.card Answer) :
    eventMass (fun table => ∃ i, markedFailure zero (program i) table) ≤ charge := by
  apply union_bound
  intro i
  apply (adaptive_exhaustion zero (program i)).trans
  have hp : (0 : ℚ) < (p : ℚ) := by norm_num [p]
  apply one_div_le_one_div_of_le (pow_pos hp _)
  exact pow_le_pow_left₀ hp.le (by exact_mod_cast cardinality) k

#print axioms adaptive_exhaustion
#print axioms source_exhaustion
#print axioms adaptive_union
end R1Z.ProverCommitAdaptiveFuel23
