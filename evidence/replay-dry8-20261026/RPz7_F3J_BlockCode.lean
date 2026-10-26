import RPz7_F3J_BlockCalls
import RPz7_AuS1_Trace
import RPz7_S1SemanticCodeSampleBlockExactV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_BlockCode
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog

theorem sample {Hash : Type} {D : aspis_core.Digest32 Hash}
    {before after : r1_wire.SemanticTranscript Hash} {row : U8} {framed : Slice U8}
    {block : Array U8 32#usize} (c : F3J_BlockCalls.Calls D before after row framed block) :
    observe (run (S1SemanticCode.sampleBlock D before row framed)).1=F3J_BlockCalls.log c := by
  have rowEq : row=before.next_row := c.row_eq
  have addTag : 160#u8+row=ok c.tag := by
    have hv := c.tag_value
    obtain ⟨r,call,value⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=160#u8) (y:=row) (by scalar_tac))
    have eq : r=c.tag := by scalar_tac
    simpa only [eq] using call
  have addNext : before.next_row+1#u8=ok c.next := by
    have hv := c.next_value
    have beforeVal := congrArg UScalar.val rowEq
    obtain ⟨r,call,value⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=before.next_row) (y:=1#u8) (by scalar_tac))
    have eq : r=c.next := by scalar_tac
    simpa only [eq] using call
  have ha := c.absorb
  have hb := c.squeeze
  have hs := c.advance
  unfold TranscriptStep.absorbParts at ha
  unfold TranscriptStep.readParts at hb hs
  unfold S1SemanticCode.sampleBlock
  have sameRow : (row != before.next_row)=false := by simp [rowEq]
  simp only [sameRow,Bool.false_eq_true,if_false,addTag,addNext]
  simp only [effects,Bind.bind,Pure.pure,PreparedHashCode.bind,run,lift,liftM,MonadLift.monadLift,MonadLiftT.monadLift,ha,hb,hs,
    observe,List.flatMap_cons,List.flatMap_nil,List.singleton_append,F3J_BlockCalls.log]
  rfl

#print axioms sample
end AspisR1.F3J_BlockCode
end
