import F3J_SourceBlockValue
import S1SemanticCodeSemanticValidatedExactV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_ValidatedLog
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog

theorem semantic {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) (below : c.row.val<25) :
    observe (run (S1SemanticCode.semanticValidated D c.before c.record)).1=callLog c := by
  have guard : (c.record.row > 24#u8)=false := by
    rw [c.record_row]
    simp only [gt_iff_lt,decide_eq_false_iff_not]
    scalar_tac
  unfold S1SemanticCode.semanticValidated
  simp only [r1_wire.ValidatedRecord.impl.row,r1_wire.ValidatedRecord.impl.framed,
    guard,Bool.false_eq_true,if_false,run,Bind.bind,Pure.pure,PreparedHashCode.bind,liftM,
    MonadLift.monadLift,MonadLiftT.monadLift]
  change observe (run (PreparedHashCode.bind
    (S1SemanticCode.sampleBlock D c.before c.record.row c.record.framed) _)).1=_
  rw [c.record_row,AuS1_Trace.run_bind,run_value,F3J_SourceBlockValue.returned]
  simp only [AuS1_Trace.continueRun]
  simp only [Bind.bind,Pure.pure,PreparedHashCode.bind,run,lift,liftM,
    MonadLift.monadLift,MonadLiftT.monadLift,core.result.Result.Insts.CoreOpsTry.branch,
    c.sample,observe,List.flatMap_append,List.flatMap_nil,List.append_nil]
  exact F3J_SourceBlock.sample c below

#print axioms semantic
end AspisR1.F3J_ValidatedLog
end
