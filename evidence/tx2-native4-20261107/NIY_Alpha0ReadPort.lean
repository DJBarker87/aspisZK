import NIY_Alpha1ReadPort
import NIY_AfterAlpha0
import NIY_C_AfterAlpha0
import NIL_PortBind
set_option autoImplicit false
noncomputable section
namespace NIY_Alpha0ReadPort
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport NIL_ResultReverse AspisR1
open NID_ResumeEmission

theorem source (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 (state : Array U8 32#usize) (a3 : Array U8 32#usize) (a4 : Array U8 32#usize) (val : aspis_core.field.wide_exact.WideExact) (val1 : aspis_core.field.wide_exact.WideExact) (r6 : verifier.Reader) :
 NIL_StatePort.reply (NIY_AfterKappa.suffix reserved d bytes v end1 i4 state a3 a4 val val1 r6)=
 NIY_C_AfterKappa.suffix (CheckpointBytes4Ops.ops reserved) bytes (variant v) end1 i4 state a3 a4 (e val) (e val1) (reader r6) := by
 with_unfolding_all rw [NIY_AfterAlpha0.source,NIY_C_AfterAlpha0.source]
 unfold NIL_StatePort.reply NIL_FreshOps.readE
 apply NIL_PortBind.read unE unReader NIL_StatePort.pair
 intro value out
 have h := NIY_Alpha1ReadPort.source reserved d bytes v end1 i4 state a3 a4 val val1 (unE value) (unReader out)
 simpa only [NIL_StatePort.reply,e_reverse,reader_reverse] using h
#print axioms source
end NIY_Alpha0ReadPort
