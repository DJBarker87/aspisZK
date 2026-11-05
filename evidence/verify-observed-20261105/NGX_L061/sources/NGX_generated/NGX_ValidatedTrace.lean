import NGX_Validated
import NGX_SamplerStages
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1PublicPreparation.PreparedHashCode
namespace AspisR1.NGX_ValidatedTrace
abbrev T (H : Type) := r1_wire.SemanticTranscript H
abbrev Bytes32 := Array U8 32#usize

theorem rejected {H : Type} (D : aspis_core.Digest32 H)
 (self : T H) (record1 : r1_wire.ValidatedRecord) (outside : record1.row>24#u8) :
 run (S1SemanticCode.semanticValidated D self record1)=([],ok (.Err .InvalidRow,self)) := by
 unfold S1SemanticCode.semanticValidated r1_wire.ValidatedRecord.impl.row
 simp only [NGX_CodeTrace.lift_bind, outside,if_pos,NGX_CodeTrace.pure_run]

theorem returned {H : Type} (D : aspis_core.Digest32 H)
 (self : T H) (record1 : r1_wire.ValidatedRecord) (tag next : U8)
 (absorbed block final : Bytes32) (q : aspis_core.field.QM31)
 (allowed : ¬record1.row>24#u8) (same : record1.row=self.next_row)
 (htag : (160#u8+record1.row : Result U8)=ok tag)
 (hnext : (self.next_row+1#u8 : Result U8)=ok next)
 (first : D.digest self.hash (NGX_SemanticSample.absorbParts self.state tag record1.framed)=ok absorbed)
 (second : D.digest self.hash (NGX_SemanticSample.readParts absorbed 1#u8)=ok block)
 (third : D.digest self.hash (NGX_SemanticSample.readParts absorbed 2#u8)=ok final)
 (native : NGT_Reduction.K block q) :
 run (S1SemanticCode.semanticValidated D self record1)=
 ([Event.digest D self.hash (NGX_SemanticSample.absorbParts self.state tag record1.framed) (ok absorbed),
 Event.digest D self.hash (NGX_SemanticSample.readParts absorbed 1#u8) (ok block),
 Event.digest D self.hash (NGX_SemanticSample.readParts absorbed 2#u8) (ok final)],
 ok (.Ok q,{state:=final,hash:=self.hash,next_row:=next})) := by
 have sample := NGX_SampleTrace.returned D self record1.row tag next record1.framed absorbed block final same htag hnext first second third
 have packing := NGX_SamplerStages.sample native
 unfold S1SemanticCode.semanticValidated r1_wire.ValidatedRecord.impl.row r1_wire.ValidatedRecord.impl.framed
 simp only [NGX_CodeTrace.lift_bind,if_neg allowed]
 rw [NGX_RunBind.bind_run,sample]
 simp only [NGX_RunBind.appendResult,NGX_CodeTrace.lift_bind]
 simp only [core.result.Result.Insts.CoreOpsTry.branch,NGX_CodeTrace.lift_bind,packing,NGX_CodeTrace.pure_run,List.append_nil]
#print axioms rejected
#print axioms returned
end AspisR1.NGX_ValidatedTrace
