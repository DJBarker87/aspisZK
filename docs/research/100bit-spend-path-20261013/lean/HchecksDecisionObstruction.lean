import R1LiteralAcceptanceTerminal

/-! A free terminal decision cannot imply R16. This counterexample is a model
statement, not an attack on the frozen deployed verifier. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.HchecksDecisionObstruction
open AspisV8R19.MemoizedProgramLaw

/-- Even a fully sampled 33-row run can accept under the free decision while
its public has no strict parse. This holds for every protocol decoder. -/
theorem free_decision_counterexample
    (decoder : LiteralByteProtocol.Decoder)
    (H : AspisV8R19.DuplexFrames.Bytes → LiteralByteProtocol.State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) :
    (eval H (FS2.verifier (LiteralByteProtocol.protocol decoder)
      (fun _ _ => true) ({pub with pubBytes := [], initFits := by have h := pub.initFits; simp only [List.length_nil]; omega}) pf)).2 = true ∧
    ¬ Nonempty (LiteralAcceptanceTerminal.Checks ({pub with pubBytes := [], initFits := by have h := pub.initFits; simp only [List.length_nil]; omega})
      ((LiteralByteProtocol.protocol decoder).transcript H
        ({pub with pubBytes := [], initFits := by have h := pub.initFits; simp only [List.length_nil]; omega}) pf 33).rounds) := by
  constructor
  · rw [FS2.verifier_eval]
  · rintro ⟨checks⟩
    have h := checks.publicParsed
    simp only [SemanticPublicWire.parsePublic, SemanticPublicWire.decode,
      Option.bind_none] at h
    cases h

#print axioms free_decision_counterexample
end AspisR1.HchecksDecisionObstruction
end
