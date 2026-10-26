import F3L_SamplerStatement
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_ParsedSampler
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem parsed (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (n : Nat) (pub : LiteralTranscript.Public)
    (h : ∃ decoded,SemanticPublicWire.parsePublic pub.pubBytes=some decoded) :
    ∃ decoded,SemanticPublicWire.parsePublic (eval H
      (F3J_SamplerRun.program pf 0 n (FS.emptyPrefix pub))).2.statement.pubBytes=some decoded := by
  rw [F3L_SamplerStatement.statement]
  exact h

#print axioms parsed
end AspisR1.F3L_ParsedSampler
end
