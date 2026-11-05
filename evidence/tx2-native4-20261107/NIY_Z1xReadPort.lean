import NIY_Z1yReadPort
import NIY_AfterZ1x
import NIY_C_AfterZ1x
import NIL_PortBind
set_option autoImplicit false
noncomputable section
namespace NIY_Z1xReadPort
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport NIL_ResultReverse AspisR1
open NID_ResumeEmission

theorem source (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 (state : Array U8 32#usize) (a3 : Array U8 32#usize) (a4 : Array U8 32#usize) (val : aspis_core.field.wide_exact.WideExact) (val1 : aspis_core.field.wide_exact.WideExact) (val2 : aspis_core.field.wide_exact.WideExact) (val3 : aspis_core.field.wide_exact.WideExact) (val4 : aspis_core.field.QM31) (queries : Array U32 22#usize) (semantic_alpha : Array aspis_core.field.QM31 10#usize) (val6 : aspis_core.field.QM31) (val7 : aspis_core.field.QM31) (r40 : verifier.Reader) :
 NIL_StatePort.reply (NIY_AfterZ0y.suffix reserved d bytes v end1 i4 state a3 a4 val val1 val2 val3 val4 queries semantic_alpha val6 val7 r40)=
 NIY_C_AfterZ0y.suffix (CheckpointBytes4Ops.ops reserved) bytes (variant v) end1 i4 state a3 a4 (e val) (e val1) (e val2) (e val3) (k val4) queries (array k semantic_alpha) (k val6) (k val7) (reader r40) := by
 with_unfolding_all rw [NIY_AfterZ1x.source,NIY_C_AfterZ1x.source]
 unfold NIL_StatePort.reply NIL_FreshOps.readK
 apply NIL_PortBind.read unK unReader NIL_StatePort.pair
 intro value out
 have h := NIY_Z1yReadPort.source reserved d bytes v end1 i4 state a3 a4 val val1 val2 val3 val4 queries semantic_alpha val6 val7 (unK value) (unReader out)
 simpa only [NIL_StatePort.reply,k_reverse,reader_reverse] using h
#print axioms source
end NIY_Z1xReadPort
