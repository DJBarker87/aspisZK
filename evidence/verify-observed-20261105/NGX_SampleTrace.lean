import NGX_CodeTrace
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1PublicPreparation.PreparedHashCode
namespace AspisR1.NGX_SampleTrace
abbrev Bytes32 := Array U8 32#usize

theorem rejected {H : Type} (D : aspis_core.Digest32 H)
 (self : r1_wire.SemanticTranscript H) (row : U8) (framed : Slice U8)
 (different : row≠self.next_row) :
 run (S1SemanticCode.sampleBlock D self row framed)=
  ([],ok (.Err (.RowOrder self.next_row row),self)) := by
 unfold S1SemanticCode.sampleBlock
 simp only [bne_iff_ne]
 rw [if_pos different]
 rfl

theorem returned {H : Type} (D : aspis_core.Digest32 H)
 (self : r1_wire.SemanticTranscript H) (row tag next : U8) (framed : Slice U8)
 (absorbed block final : Bytes32)
 (same : row=self.next_row)
 (htag : (160#u8+row : Result U8)=ok tag)
 (hnext : (self.next_row+1#u8 : Result U8)=ok next)
 (first : D.digest self.hash (NGX_SemanticSample.absorbParts self.state tag framed)=ok absorbed)
 (second : D.digest self.hash (NGX_SemanticSample.readParts absorbed 1#u8)=ok block)
 (third : D.digest self.hash (NGX_SemanticSample.readParts absorbed 2#u8)=ok final) :
 run (S1SemanticCode.sampleBlock D self row framed)=
 ([Event.digest D self.hash (NGX_SemanticSample.absorbParts self.state tag framed) (ok absorbed),
   Event.digest D self.hash (NGX_SemanticSample.readParts absorbed 1#u8) (ok block),
   Event.digest D self.hash (NGX_SemanticSample.readParts absorbed 2#u8) (ok final)],
  ok (.Ok block,{state:=final,hash:=self.hash,next_row:=next})) := by
 subst row
 unfold S1SemanticCode.sampleBlock
 simp only [bne_self_eq_false,Bool.false_eq_true,if_false]
 simp only [NGX_SemanticSample.absorbParts,NGX_SemanticSample.readParts] at first second third ⊢
 simp only [lift,htag,hnext,NGX_CodeTrace.lift_bind,NGX_CodeTrace.digest_bind,
   NGX_CodeTrace.pure_run,first,second,third]
#print axioms rejected
#print axioms returned
end AspisR1.NGX_SampleTrace
