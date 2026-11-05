import NIY_SemanticPort
import NIY_C_ValidationCut
import NIY_SectionBind
set_option autoImplicit false
noncomputable section
namespace NIY_ValidationPort
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport NIL_ResultReverse AspisR1
open NID_ResumeEmission

theorem source (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 (state : Array U8 32#usize) (a3 : Array U8 32#usize) (a4 : Array U8 32#usize) (val : aspis_core.field.wide_exact.WideExact) (val1 : aspis_core.field.wide_exact.WideExact) (val2 : aspis_core.field.wide_exact.WideExact) (val3 : aspis_core.field.wide_exact.WideExact) (val4 : aspis_core.field.QM31) (queries : Array U32 22#usize) (r34 : verifier.Reader) :
 NIL_StatePort.reply (NIY_QueryCut.afterQueries reserved d bytes v end1 i4 state a3 a4 val val1 val2 val3 val4 queries r34)=
 NIY_C_QueryCut.afterQueries (CheckpointBytes4Ops.ops reserved) bytes (variant v) end1 i4 state a3 a4 (e val) (e val1) (e val2) (e val3) (k val4) queries (reader r34) := by
 with_unfolding_all rw [NIY_ValidationCut.source,NIY_C_ValidationCut.source]
 unfold NIL_StatePort.reply NIL_FreshOps.validate
 apply NIY_SectionBind.sectionReply
 intro unit
 have h := NIY_SemanticPort.source reserved d bytes v end1 i4 state a3 a4 val val1 val2 val3 val4 queries r34
 simpa only [NIL_StatePort.reply] using h
#print axioms source
end NIY_ValidationPort
