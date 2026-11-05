import NIY_QueryPort
import NIY_AfterRho
import NIY_C_AfterRho
import NIL_PortBind
set_option autoImplicit false
noncomputable section
namespace NIY_RhoReadPort
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport NIL_ResultReverse AspisR1
open NID_ResumeEmission

theorem source (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 (state : Array U8 32#usize) (a3 : Array U8 32#usize) (a4 : Array U8 32#usize) (val : aspis_core.field.wide_exact.WideExact) (val1 : aspis_core.field.wide_exact.WideExact) (val2 : aspis_core.field.wide_exact.WideExact) (val3 : aspis_core.field.wide_exact.WideExact) (r10 : verifier.Reader) :
 NIL_StatePort.reply (NIY_AfterAlpha1.suffix reserved d bytes v end1 i4 state a3 a4 val val1 val2 val3 r10)=
 NIY_C_AfterAlpha1.suffix (CheckpointBytes4Ops.ops reserved) bytes (variant v) end1 i4 state a3 a4 (e val) (e val1) (e val2) (e val3) (reader r10) := by
 with_unfolding_all rw [NIY_AfterRho.source,NIY_C_AfterRho.source]
 unfold NIL_StatePort.reply NIL_FreshOps.readK
 apply NIL_PortBind.read unK unReader NIL_StatePort.pair
 intro value out
 have h := NIY_QueryPort.source reserved d bytes v end1 i4 state a3 a4 val val1 val2 val3 (unK value) (unReader out)
 simpa only [NIL_StatePort.reply,k_reverse,reader_reverse] using h
#print axioms source
end NIY_RhoReadPort
