import F3J_ValidatedLog
import F3J_SourceBlockValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_SemanticStep
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog

theorem returned {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) (below : c.row.val<25) :
    erase (S1SemanticCode.semanticValidated D c.before c.record)=ok (.Ok c.q,c.after) := by
  have guard : (c.record.row > 24#u8)=false := by
    rw [c.record_row]
    simp only [gt_iff_lt,decide_eq_false_iff_not]
    scalar_tac
  unfold S1SemanticCode.semanticValidated
  simp only [r1_wire.ValidatedRecord.impl.row,r1_wire.ValidatedRecord.impl.framed,
    guard,Bool.false_eq_true,if_false]
  change erase (PreparedHashCode.bind
    (S1SemanticCode.sampleBlock D c.before c.record.row c.record.framed) _)=_
  rw [c.record_row,AuS1_Trace.erase_bind,F3J_SourceBlockValue.returned]
  simpa only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] using c.sample

#print axioms returned
end AspisR1.F3R_SemanticStep
end
