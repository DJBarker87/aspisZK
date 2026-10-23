import OraclePortFrozen2Join

/-! Two-pass lifting under the one-way source acceptance fact actually needed.
The backward fact remains explicit; a raw accepted-run join does not provide
it. This is a lifting rule, not the frozen implementation instance. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.VTop_Annotation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7 OraclePortFrozen2Join

theorem two_pass (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (raw : AcceptedVerifierJoin rust (verifier D OraclePortFrozen2.dV_frozen2))
    (backward : ∀ w i H, (eval H (rust (enrich w i))).2 = true →
      (eval H (rust i)).2 = true) : AcceptedRunJoin D rust := by
  refine ⟨raw, ?_⟩
  intro P H accepted
  have before : (eval H (originalWith rust P)).2.2 = true := by
    have second := accepted
    rw [annotatedWith_eval, originalWith_eval] at second
    rw [originalWith_eval]
    exact backward _ _ H second
  have firstPass : eval H (originalWith rust P) =
      eval H (originalWith (verifier D OraclePortFrozen2.dV_frozen2) P) := by
    rw [originalWith_eval] at before
    simp only [originalWith_eval, raw H (eval H P).2 before]
  rw [annotatedWith_eval, firstPass] at accepted ⊢
  have secondPass := raw H _ accepted
  change _ = eval H (annotatedWith D (verifier D OraclePortFrozen2.dV_frozen2) P)
  simp only [annotatedWith_eval, secondPass]

#print axioms two_pass
end AspisR1.VTop_Annotation
end
