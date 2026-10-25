import Hiq_ObservedInputs
import Hiq_RecordedBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_BindingFailure
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound

def failure {A : Type} (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (v : View Bytes State (View Bytes State A)) : Prop :=
  let pair := select v.2.2
  R9PoolRuntimeBinding.digestMatches (Hiq_ObservedHash.hash v.1) pair.1 pair.2 ∧ pair.2 ≠ pair.1

theorem subset {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (Q : Nat) (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q)
    (H : Bytes → State) (failed : failure select (eval H (Hiq_RecordedJoint.program source project select))) :
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+1044)
      (eval H (Hiq_RecordedJoint.program source project select)) := by
  rcases failed with ⟨matched,different⟩
  obtain ⟨wp,wu,cp,cu⟩ := Hiq_ObservedInputs.hash_values source project select H
  have actual : R9PoolRuntimeBinding.digestMatches H
      (select (eval H (Hiq_RecordedJoint.program source project select)).2.2).1
      (select (eval H (Hiq_RecordedJoint.program source project select)).2.2).2 := by
    unfold R9PoolRuntimeBinding.digestMatches at matched ⊢
    simpa only [wp,wu,cp,cu] using matched
  have association : (eval H (Hiq_RecordedJoint.program source project select)).2.2 = (eval H source).2 :=
    congrArg Prod.snd (Hiq_RecordedJoint.source_view source project select H)
  rw [association] at actual different
  rcases Hiq_JointBinding.binding_or_collision SelectedTranscriptParams.params.iv source project select Q budget H with bad | good
  · simpa only [Hiq_RecordedJoint.evaluation,BinRawByteCollisionTargets.event] using bad
  · exact False.elim (different (R9PoolRuntimeBinding.accepted_same_inputs H _ _ good actual))

theorem mass {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (Q : Nat) (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q) :
    lazyMean (Hiq_RecordedJoint.program source project select) emptyTable (fun v => indicator (failure select v)) ≤
      6*((Q+1044 : Nat) : Rat)^2/(256^32 : Rat) := by
  apply (OracleProgramLawExt.lazyMean_le_of_eval _ _ _
    (fun v => indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+1044) v))
    (fun H => indicator_mono (subset source project select Q budget H))).trans
  exact Hiq_RecordedBudget.collision source project select Q budget

#print axioms subset
#print axioms mass
end AspisR1.Hiq_BindingFailure
end
