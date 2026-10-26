import RPz7_F3J_BlockCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_BlockCodeValue
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog

theorem returned {Hash : Type} {D : aspis_core.Digest32 Hash}
    {before after : r1_wire.SemanticTranscript Hash} {row : U8} {framed : Slice U8}
    {block : Array U8 32#usize} (c : F3J_BlockCalls.Calls D before after row framed block) :
    erase (S1SemanticCode.sampleBlock D before row framed)=ok (.Ok block,after) := by
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
  rw [S1SemanticCode.sampleBlock_erasure,
    TranscriptStep.step_of_add D before row c.tag c.next framed rowEq addTag addNext,
    c.absorb,bind_tc_ok,c.squeeze,bind_tc_ok,c.advance,bind_tc_ok]
  exact congrArg (fun t => ok ((core.result.Result.Ok block : core.result.Result (Array U8 32#usize) r1_wire.Error),t)) c.carried.symm

#print axioms returned
end AspisR1.F3J_BlockCodeValue
end
