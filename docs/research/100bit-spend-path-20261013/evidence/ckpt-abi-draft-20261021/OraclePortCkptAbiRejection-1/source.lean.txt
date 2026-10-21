import OraclePortCkptAbiReference

/-! A precise rejection-order obstruction to treating C5's eager resumer as
an all-input source refinement. Only log lengths are compared, so different
return types cannot disguise the disagreement. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCkptAbiRejection
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OraclePortCompactDraft OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5
open OraclePortCkptAbiReference
attribute [local instance] Classical.propDecidable

theorem first_digest_failure (H : Bytes → State) (stored pub ck : Bytes)
    (header : Header ck) (bad : slice ck 16 32 ≠ bytes (H stored)) :
    eval H (OraclePortCkptAbiReference.resume stored pub ck) =
      ([(stored,H stored)],none) := by
  rw [resume_eval,if_pos header,if_neg bad]

theorem public_digest_failure (H : Bytes → State) (stored pub ck : Bytes)
    (header : Header ck) (proof : slice ck 16 32 = bytes (H stored))
    (bad : slice ck 48 32 ≠ bytes (H pub)) :
    eval H (OraclePortCkptAbiReference.resume stored pub ck) =
      ([(stored,H stored),(pub,H pub)],none) := by
  rw [resume_eval,if_pos header,if_pos proof,if_neg bad]

theorem c5_eager_log_mismatch (H : Bytes → State) (stored pub ck : Bytes)
    (d : MatchingSupport.Data E) (header : Header ck)
    (bad : slice ck 16 32 ≠ bytes (H stored)) :
    (eval H (OraclePortCkptAbiReference.resume stored pub ck)).1 ≠
      (eval H (OraclePortCheckpointOracleC5.resumer pub d ⟨stored,ck⟩)).1 := by
  intro same
  have sizes := congrArg List.length same
  rw [first_digest_failure H stored pub ck header bad] at sizes
  have eager := OraclePortCheckpointOracleC5.resumer_reads H pub d ⟨stored,ck⟩
  change 1 = _ at sizes
  rw [eager] at sizes
  contradiction

#print axioms first_digest_failure
#print axioms public_digest_failure
#print axioms c5_eager_log_mismatch
end AspisR1.OraclePortCkptAbiRejection
end
