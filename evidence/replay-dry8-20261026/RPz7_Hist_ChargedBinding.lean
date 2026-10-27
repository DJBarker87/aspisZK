import RPz7_Hist_AuditQueries
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_ChargedBinding
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.CausalFirstHitUnionBound
open AspisV8PairedCommitment Hist_AuditQueries

theorem result_preserved {A : Type} (H : Bytes → State) (source : Program Bytes State A)
    (select : A → Inputs × Inputs) :
    (eval H (augmented source select)).2 = (eval H source).2 := by
  rw [augmented_eval]

/-- The four complete byte strings are actual reads of the charged augmented
experiment, even if none occurred in the preceding source prefix. -/
theorem all_read {A : Type} (H : Bytes → State) (source : Program Bytes State A)
    (select : A → Inputs × Inputs) :
    let pair := select (eval H source).2
    let log := (eval H (augmented source select)).1
    Read log pair.1.proof ∧ Read log pair.1.pub ∧
      Read log pair.2.proof ∧ Read log pair.2.pub := by
  dsimp only
  rw [augmented_eval,audit_eval]
  simp [Read]

/-- No supplied log, hash injectivity, read-provenance or P2Prime premise.
The containing source and selection function are fixed BEFORE H. -/
theorem binding_or_collision {A : Type} (iv : State) (source : Program Bytes State A)
    (select : A → Inputs × Inputs) (Q : Nat)
    (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q)
    (H : Bytes → State) :
    BinRawByteCollisionTargets.event iv (Q+4) (eval H (augmented source select)) ∨
      R9PoolRuntimeBinding.P2Prime H (select (eval H source).2).1 (select (eval H source).2).2 := by
  obtain ⟨wp,wu,cp,cu⟩ := all_read H source select
  exact Hist_P2Prime.binding_or_collision iv H (eval H (augmented source select)).1 (Q+4)
    (fun q member => Op5I_AcceptedCarrierCounterexample.evaluated_reply H _ q member)
    (augmented_budget source select Q budget H) _ _ wp wu cp cu

/-- The additional loss is explicit. If an existing canonical replay is already
charged1040 reads, this audit charges4 more: use Q+1044, not uncharged reads. -/
theorem collision_bound {A : Type} (iv : State) (source : Program Bytes State A)
    (select : A → Inputs × Inputs) (Q : Nat)
    (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q) :
    lazyMean (augmented source select) emptyTable
      (fun view => indicator (BinRawByteCollisionTargets.event iv (Q+4) view)) ≤
      6 * ((Q+4 : Nat) : Rat)^2 / (256^32 : Rat) :=
  BinRawByteCollisionTargets.mass iv (Q+4) _ (augmented_budget source select Q budget)

#print axioms result_preserved
#print axioms all_read
#print axioms binding_or_collision
#print axioms collision_bound
end AspisR1.Hist_ChargedBinding
end
