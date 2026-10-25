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
  have sameRow : (c.row != c.before.next_row)=false := by simp [rowEq]
  simp only [sameRow,Bool.false_eq_true,if_false,addTag,addNext]
  simp only [effects,PreparedHashCode.bind,run,lift,liftM,MonadLift.monadLift,MonadLiftT.monadLift,bind_tc_ok,addNext,c.absorb,c.read1,c.read2,
    observe,List.flatMap_cons,List.flatMap_nil,List.singleton_append,callLog]

#print axioms sample
end AspisR1.F3J_SourceBlock
end
