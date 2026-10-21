import OraclePortCheckpoint
import HchecksAccumulator

/-! A reached-state checkpoint: the prepared inputs are retained, the saved
accumulator is computed after ten steps, and resume executes twelve further
steps. No external accumulator is accepted. Physical byte refinement is not
asserted here; see OraclePortTerminalCarrierAuditC3 for the carrier obstruction. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCheckpointStateC3
open scoped BigOperators
open QueryAccumulator
variable {K E : Type} [Field K] [Field E]

structure Prepared (K E : Type) [Field K] [Field E] where
  iota : K →+* E
  rho : K
  values : Fin 22 → E
  basis : Fin 22 → Fin 64 → K

structure Saved (K E : Type) [Field K] [Field E] where
  prepared : Prepared K E
  accumulator : QueryAccumulator.State K E

def advance (p : Prepared K E) : Nat → QueryAccumulator.State K E → QueryAccumulator.State K E
  | 0, s => s
  | n+1, s => step p.iota p.rho (extend22 p.values) (extend22 p.basis) (advance p n s)

theorem advance_run (p : Prepared K E) (n k : Nat) :
    advance p n (run p.iota p.rho (extend22 p.values) (extend22 p.basis) k) =
      run p.iota p.rho (extend22 p.values) (extend22 p.basis) (k+n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [advance,ih]; rfl

def write (p : Prepared K E) : Saved K E :=
  ⟨p,run p.iota p.rho (extend22 p.values) (extend22 p.basis) 10⟩

def resume (s : Saved K E) : Saved K E :=
  ⟨s.prepared,advance s.prepared 12 s.accumulator⟩

theorem saved_next (p : Prepared K E) : (write p).accumulator.next = 10 :=
  run_next _ _ _ _ _

theorem resumed_state (p : Prepared K E) :
    (resume (write p)).prepared = p ∧
    (resume (write p)).accumulator = run22 p.iota p.rho p.values p.basis := by
  constructor
  · rfl
  · exact advance_run p 12 10

theorem resumed_fields (p : Prepared K E) :
    (resume (write p)).accumulator.next = 22 ∧
    (resume (write p)).accumulator.power = p.rho^22 ∧
    (∀ l, (resume (write p)).accumulator.weights l =
      ∑ j : Fin 22, p.rho^j.val * p.basis j l) ∧
    (resume (write p)).accumulator.rhs =
      ∑ j : Fin 22, (p.iota p.rho)^j.val * p.values j := by
  rw [(resumed_state p).2]
  exact run22_closed_forms _ _ _ _

variable [Fintype K] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) E] [Algebra (ZMod AspisCircleGroupOrder.P) K]

def fromData (iota : K →+* E) (rho : K) (data : MatchingSupport.Data E)
    (q : Fin 22 → Fin 262144) : Prepared K E :=
  ⟨iota,rho,QueryResidualBridge.values data q,QueryResidualBridge.basis q⟩

/-- The resumed arithmetic relation is exactly the existing R14 model sum. -/
theorem finish_iff (iota : K →+* E) (rho : K) (data : MatchingSupport.Data E)
    (q : Fin 22 → Fin 262144) :
    (∑ l : Fin 64, data.f l * iota
      ((resume (write (fromData iota rho data q))).accumulator.weights l)) =
      (resume (write (fromData iota rho data q))).accumulator.rhs ↔
    HchecksAccumulator.ClosedSum iota data q rho := by
  rw [(resumed_state _).2]
  simp only [fromData,run22_weights,run22_rhs,HchecksAccumulator.ClosedSum]

#print axioms advance_run
#print axioms saved_next
#print axioms resumed_state
#print axioms resumed_fields
#print axioms finish_iff
end AspisR1.OraclePortCheckpointStateC3
end
