import F3L_TypedFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_LateFieldEquality
open AspisV8R19.SourceDuplexStep

theorem rho_state (Q : LiteralTranscript.Prefix)
    (i : RecordedBinaryExperimentBin.SourceInputs)
    (fields : D0InstanceAdmission.Fields (LiteralTranscript.erasePrefix Q) i)
    (m : LiteralTranscript.Message) (rho : LiteralTranscript.E) (state : State)
    (entry : Q.rounds[32]?=some (m,(TranscriptView.Value.ordinary rho,state))) :
    i.rho=rho ∧ i.state32=state := by
  have erased : (LiteralTranscript.erasePrefix Q).rounds[32]?=
      some (LiteralTranscript.erase m,(TranscriptView.Value.ordinary rho,state)) := by
    simp only [LiteralTranscript.erasePrefix,List.getElem?_map,entry,Option.map_some]
  have same := Option.some.inj (fields.2.2.1.symm.trans erased)
  have value := congrArg (fun x : RawCutTranscriptRun.ErasedMessage × LiteralTranscript.Challenge => x.2.1) same
  exact ⟨TranscriptView.Value.ordinary.inj value,congrArg (fun x => x.2.2) same⟩

#print axioms rho_state
end AspisR1.F3L_LateFieldEquality
end
