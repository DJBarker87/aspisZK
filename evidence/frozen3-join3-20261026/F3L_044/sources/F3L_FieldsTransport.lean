import F3L_SamplerAt
import D0InstanceAdmission
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_FieldsTransport
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem fields (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (row a b : Nat) (P : LiteralTranscript.Prefix)
    (h : ∃ i,D0InstanceAdmission.Fields (LiteralTranscript.erasePrefix (eval H
      (F3J_SamplerRun.program pf (row+a) b (eval H (F3J_SamplerRun.program pf row a P)).2)).2) i) :
    ∃ i,D0InstanceAdmission.Fields (LiteralTranscript.erasePrefix (eval H
      (F3J_SamplerRun.program pf row (a+b) P)).2) i := by
  rw [F3J_SamplerCompose.value H pf row a b P]
  exact h

#print axioms fields
end AspisR1.F3L_FieldsTransport
end
