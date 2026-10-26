import RPz7_F3J_BlockCodeValue
import RPz7_PAln_CircleCalls
import RPz7_S1SemanticCodeCircleValidatedV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_CircleCode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode

theorem first {Hash : Type} {D : aspis_core.Digest32 Hash}
    {before after : r1_wire.SemanticTranscript Hash} (record : r1_wire.ValidatedRecord)
    {block : Array U8 32#usize} (c : F3J_BlockCalls.Calls D before after 25#u8 record.framed block)
    (B : FinishModel.Boundaries) (point : aspis_core.circle.SecureCirclePoint)
    (row : record.row=25#u8) (circle : B.circle block .First=ok point) :
    observe (run (S1SemanticCode.circleValidated B D before record)).1=F3J_BlockCalls.log c := by
  unfold S1SemanticCode.circleValidated
  simp only [r1_wire.ValidatedRecord.impl.row,r1_wire.ValidatedRecord.impl.framed,
    row,Bind.bind,Pure.pure,PreparedHashCode.bind,run,liftM,
    MonadLift.monadLift,MonadLiftT.monadLift]
  change observe (run (PreparedHashCode.bind
    (S1SemanticCode.sampleBlock D before 25#u8 record.framed) _)).1=_
  rw [AuS1_Trace.run_bind,run_value,F3J_BlockCodeValue.returned c]
  simp only [AuS1_Trace.continueRun,Bind.bind,Pure.pure,PreparedHashCode.bind,run,liftM,
    MonadLift.monadLift,MonadLiftT.monadLift,core.result.Result.Insts.CoreOpsTry.branch,
    circle,observe,List.flatMap_append,List.flatMap_nil,List.append_nil]
  exact F3J_BlockCode.sample c

theorem second {Hash : Type} {D : aspis_core.Digest32 Hash}
    {before after : r1_wire.SemanticTranscript Hash} (record : r1_wire.ValidatedRecord)
    {block : Array U8 32#usize} (c : F3J_BlockCalls.Calls D before after 26#u8 record.framed block)
    (B : FinishModel.Boundaries) (point : aspis_core.circle.SecureCirclePoint)
    (row : record.row=26#u8) (circle : B.circle block .Second=ok point) :
    observe (run (S1SemanticCode.circleValidated B D before record)).1=F3J_BlockCalls.log c := by
  unfold S1SemanticCode.circleValidated
  simp only [r1_wire.ValidatedRecord.impl.row,r1_wire.ValidatedRecord.impl.framed,
    row,Bind.bind,Pure.pure,PreparedHashCode.bind,run,liftM,
    MonadLift.monadLift,MonadLiftT.monadLift]
  change observe (run (PreparedHashCode.bind
    (S1SemanticCode.sampleBlock D before 26#u8 record.framed) _)).1=_
  rw [AuS1_Trace.run_bind,run_value,F3J_BlockCodeValue.returned c]
  simp only [AuS1_Trace.continueRun,Bind.bind,Pure.pure,PreparedHashCode.bind,run,liftM,
    MonadLift.monadLift,MonadLiftT.monadLift,core.result.Result.Insts.CoreOpsTry.branch,
    circle,observe,List.flatMap_append,List.flatMap_nil,List.append_nil]
  exact F3J_BlockCode.sample c

#print axioms first
#print axioms second
end AspisR1.F3J_CircleCode
end
