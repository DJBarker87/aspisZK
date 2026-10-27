import F3J_SourceBlock
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_SourceBlockValue
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog

theorem returned {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) :
    erase (S1SemanticCode.sampleBlock D c.before c.row c.record.framed)=ok (.Ok c.block,c.after) := by
  have rowEq : c.row=c.before.next_row := c.record_row.symm.trans c.before_row
  have addTag : 160#u8+c.row=ok c.tag := by
    have hv := c.tag_code
    rw [c.record_row] at hv
    obtain ⟨r,call,value⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=160#u8) (y:=c.row) (by scalar_tac))
    have eq : r=c.tag := by scalar_tac
    simpa only [eq] using call
  have addNext : c.before.next_row+1#u8=ok c.next := by
    have hv := c.next_row
    rw [c.record_row] at hv
    have beforeVal := congrArg UScalar.val rowEq
    obtain ⟨r,call,value⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=c.before.next_row) (y:=1#u8) (by scalar_tac))
    have eq : r=c.next := by scalar_tac
    simpa only [eq] using call
  rw [S1SemanticCode.sampleBlock_erasure,
    TranscriptStep.step_of_add D c.before c.row c.tag c.next c.record.framed rowEq addTag addNext,
    c.absorb,bind_tc_ok,c.read1,bind_tc_ok,c.read2,bind_tc_ok,c.carried]

#print axioms returned
end AspisR1.F3J_SourceBlockValue
end
