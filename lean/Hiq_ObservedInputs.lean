import Hiq_ObservedHash
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_ObservedInputs
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem reads {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) (H : Bytes → State) :
    let v := eval H (Hiq_RecordedJoint.program source project select)
    let pair := select v.2.2
    Read v.1 pair.1.proof ∧ Read v.1 pair.1.pub ∧ Read v.1 pair.2.proof ∧ Read v.1 pair.2.pub := by
  dsimp only
  rw [Hiq_RecordedJoint.evaluation]
  have h := Hist_ChargedBinding.all_read H (SdkC_Replay.augmented source project) select
  rw [Hist_JointCharge.replay_result] at h
  exact h

theorem hash_values {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) (H : Bytes → State) :
    let v := eval H (Hiq_RecordedJoint.program source project select)
    let pair := select v.2.2
    Hiq_ObservedHash.hash v.1 pair.1.proof = H pair.1.proof ∧
      Hiq_ObservedHash.hash v.1 pair.1.pub = H pair.1.pub ∧
      Hiq_ObservedHash.hash v.1 pair.2.proof = H pair.2.proof ∧
      Hiq_ObservedHash.hash v.1 pair.2.pub = H pair.2.pub := by
  dsimp only
  obtain ⟨wp,wu,cp,cu⟩ := reads source project select H
  have answers : ∀ q ∈ (eval H (Hiq_RecordedJoint.program source project select)).1, q.2 = H q.1 :=
    fun q member => Op5I_AcceptedCarrierCounterexample.evaluated_reply H _ q member
  exact ⟨Hiq_ObservedHash.consistent H _ _ wp answers,Hiq_ObservedHash.consistent H _ _ wu answers,
    Hiq_ObservedHash.consistent H _ _ cp answers,Hiq_ObservedHash.consistent H _ _ cu answers⟩

#print axioms reads
#print axioms hash_values
end AspisR1.Hiq_ObservedInputs
end
