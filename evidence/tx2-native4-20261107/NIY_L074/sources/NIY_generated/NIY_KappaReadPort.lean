import NIY_Alpha0ReadPort
import NIY_AfterKappa
import NIY_C_AfterKappa
import NIL_PortBind
set_option autoImplicit false
noncomputable section
namespace NIY_KappaReadPort
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport NIL_ResultReverse AspisR1
open NID_ResumeEmission

theorem source (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 (state a3 a4 : Array U8 32#usize) (val : aspis_core.field.wide_exact.WideExact)
 (r4 : verifier.Reader) :
 NIL_StatePort.reply (NIY_FirstECut.afterGamma reserved d bytes v end1 i4 state a3 a4 val r4)=
 NIY_C_FirstECut.afterGamma (CheckpointBytes4Ops.ops reserved) bytes (variant v) end1 i4 state a3 a4 (e val) (reader r4) := by
 with_unfolding_all rw [NIY_AfterKappa.source,NIY_C_AfterKappa.source]
 unfold NIL_StatePort.reply NIL_FreshOps.readE
 apply NIL_PortBind.read unE unReader NIL_StatePort.pair
 intro value out
 have h := NIY_Alpha0ReadPort.source reserved d bytes v end1 i4 state a3 a4 val (unE value) (unReader out)
 simpa only [NIL_StatePort.reply,e_reverse,reader_reverse] using h
#print axioms source
end NIY_KappaReadPort
