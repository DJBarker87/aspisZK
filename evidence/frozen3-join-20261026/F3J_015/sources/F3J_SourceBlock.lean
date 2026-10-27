import F3J_SemanticLog
import AuS1_Trace
import S1SemanticCodeSampleBlockExactV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_SourceBlock
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog

theorem sample {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) (below : c.row.val<25) :
    observe (run (S1SemanticCode.sampleBlock D c.before c.row c.record.framed)).1=callLog c := by
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
  unfold S1SemanticCode.sampleBlock
  have sameRow : (c.row != c.before.next_row)=false := by simp only [rowEq,bne_self]
  simp only [sameRow,Bool.false_eq_true,if_false,addTag,addNext]
  change observe (run (do
    let absorbed ← effects.digest D c.before.hash (TranscriptStep.absorbParts c.before.state c.tag c.record.framed)
    let block ← effects.digest D c.before.hash (TranscriptStep.readParts absorbed 1#u8)
    let state ← effects.digest D c.before.hash (TranscriptStep.readParts absorbed 2#u8)
    pure ((core.result.Result.Ok block : core.result.Result (Array U8 32#usize) r1_wire.Error),{c.before with state,next_row:=c.next}))).1=callLog c
  simp only [effects,bind,run,c.absorb,c.read1,c.read2,observe,List.flatMap_cons,List.flatMap_nil,
    List.singleton_append,callLog]

#print axioms sample
end AspisR1.F3J_SourceBlock
end
