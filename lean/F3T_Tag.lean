import F3T_Decision
import OraclePortSamplerPrefixDraft
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Tag
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem base_tag (D : LiteralByteProtocol.Decoder) (d : OraclePortExperiment.Decision)
    (admitted : OraclePortAdmission.admit d=d) (P : RawCutProverCompiler.Prover)
    (H : Bytes → State)
    (accepted : (eval H (OraclePortExperiment.original D d P)).2.2=true) :
    (OraclePortSamplerPrefixDraft.base D P H).2.1.1.tag=2 := by
  have tag : (eval H (OraclePortExperiment.original D d P)).2.1.1.tag=2 := by
    rw [←admitted] at accepted ⊢
    exact OraclePortAdmission.accepted_tag D d P H accepted
  rw [OraclePortSamplerPrefixDraft.output_pair] at tag
  exact tag
#print axioms base_tag
end AspisR1.F3T_Tag
end
