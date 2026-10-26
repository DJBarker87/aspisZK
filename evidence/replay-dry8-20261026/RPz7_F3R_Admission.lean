import RPz7_F3R_ModelSchedule
import RPz7_F3J_SamplerStructure
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_Admission
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem erased_valid (row : Nat) (m : LiteralTranscript.Message) (valid : LiteralTranscript.valid row m) :
    UnifiedSampler.messageValid row (LiteralTranscript.erase m) := by
  unfold LiteralTranscript.valid at valid
  split at valid <;> simp_all [LiteralTranscript.erase,UnifiedSampler.messageValid]
  all_goals cases row <;> simp_all [UnifiedSampler.messageValid]

theorem guard (D : LiteralByteProtocol.Decoder) (H : Bytes → State) (i : F3_Model.Input)
    (tag : i.semantic.value.tag=2) (valid : ∀ row,row<33 → LiteralTranscript.valid row (i.proof row))
    (fields : ∃ input,D0InstanceAdmission.Fields (LiteralTranscript.erasePrefix
      (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2) input) :
    OraclePortAdmission.Guard (LiteralTranscript.erasePrefix
      (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2) := by
  have length := F3J_SamplerRun.length H i.proof 0 33 (FS.emptyPrefix i.semantic.value)
  change (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2.rounds.length=33 at length
  have sampler := F3K_SamplerProtocol.initial D H i.semantic.value i.proof 33
  have trEq := congrArg Prod.snd sampler
  dsimp only at trEq
  refine ⟨?_,⟨?_,?_⟩,fields⟩
  · change (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2.statement.tag=2
    rw [F3J_SamplerStructure.statement]
    exact tag
  · simpa only [LiteralTranscript.erasePrefix,List.length_map] using length
  · intro row m c read
    have bound := (List.getElem?_eq_some_iff.mp read).1
    have len : (LiteralTranscript.erasePrefix
        (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2).rounds.length=33 := by
      simpa only [LiteralTranscript.erasePrefix,List.length_map] using length
    have below : row<33 := by omega
    rw [trEq] at read
    simp only [LiteralTranscript.erasePrefix,List.getElem?_map,
      LiteralByteRunFacts.transcript_index D H i.semantic.value i.proof 33 row below,
      Option.map_some,Option.some.injEq] at read
    have message := congrArg Prod.fst read
    dsimp only at message
    rw [←message]
    exact erased_valid row (i.proof row) (valid row below)

#print axioms erased_valid
#print axioms guard
end AspisR1.F3R_Admission
end
