import NIY_ValidationPort
import NIY_C_QueryCut
import NIY_QueryTransport
set_option autoImplicit false
noncomputable section
namespace NIY_QueryPort
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport NIL_ResultReverse AspisR1
open NID_ResumeEmission

theorem source (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 (state : Array U8 32#usize) (a3 : Array U8 32#usize) (a4 : Array U8 32#usize) (val : aspis_core.field.wide_exact.WideExact) (val1 : aspis_core.field.wide_exact.WideExact) (val2 : aspis_core.field.wide_exact.WideExact) (val3 : aspis_core.field.wide_exact.WideExact) (val4 : aspis_core.field.QM31) (r12 : verifier.Reader) :
 NIL_StatePort.reply (NIY_AfterRho.suffix reserved d bytes v end1 i4 state a3 a4 val val1 val2 val3 val4 r12)=
 NIY_C_AfterRho.suffix (CheckpointBytes4Ops.ops reserved) bytes (variant v) end1 i4 state a3 a4 (e val) (e val1) (e val2) (e val3) (k val4) (reader r12) := by
 with_unfolding_all rw [NIY_QueryCut.source,NIY_C_QueryCut.source]
 unfold NIL_StatePort.reply
 apply NIY_QueryTransport.continuation
 intro queries out
 have h := NIY_ValidationPort.source reserved d bytes v end1 i4 state a3 a4 val val1 val2 val3 val4 queries (unReader out)
 simpa only [NIL_StatePort.reply,reader_reverse] using h
#print axioms source
end NIY_QueryPort
