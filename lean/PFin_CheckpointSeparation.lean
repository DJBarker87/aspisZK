import PFin_ReplayBound
import F3_Checkpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_CheckpointSeparation
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem long (H : Bytes → State) (physical : F3_Model.PhysicalPublic) (stored : Bytes)
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (i : RecordedBinaryExperimentBin.SourceInputs) (v : LiteralOpeningView.View)
    (physicalLong : 514<physical.bytes.length) (storedLong : 514<stored.length) :
    ∀ entry∈(eval H (F3_Model.checkpoint physical stored p q tr i v)).1,514<entry.1.length := by
  unfold F3_Model.checkpoint
  rw [F3_Checkpoint.schedule]
  intro entry member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact storedLong
  · exact physicalLong
  · simp only [List.length_append,OraclePortCheckpointAbiC5.body_length]
    omega
  · exact storedLong
  · exact physicalLong
  · simp only [List.length_append,OraclePortCheckpointAbiC5.body_length]
    omega

theorem disjoint (H : Bytes → State) (physical : F3_Model.PhysicalPublic) (stored : Bytes)
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (i : RecordedBinaryExperimentBin.SourceInputs) (v : LiteralOpeningView.View)
    (physicalLong : 514<physical.bytes.length) (storedLong : 514<stored.length)
    (slots : List (Nat × Nat)) :
    ∀ address,Read (eval H (OraclePortFrozen2.batch p q slots)).1 address →
      ¬Read (eval H (F3_Model.checkpoint physical stored p q tr i v)).1 address := by
  intro address batchRead ckRead
  obtain ⟨batchEntry,batchMember,batchAddress⟩ := List.mem_map.mp batchRead
  obtain ⟨ckEntry,ckMember,ckAddress⟩ := List.mem_map.mp ckRead
  have small := PFin_ReplayBound.batch p q slots H batchEntry batchMember
  have large := long H physical stored p q tr i v physicalLong storedLong ckEntry ckMember
  rw [batchAddress] at small
  rw [ckAddress] at large
  omega

#print axioms long
#print axioms disjoint
end AspisR1.PFin_CheckpointSeparation
end
