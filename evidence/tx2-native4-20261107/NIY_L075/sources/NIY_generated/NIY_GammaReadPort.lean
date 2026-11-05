import NIY_KappaReadPort
import NIY_FirstECut
import NIY_C_FirstECut
import NIL_PortBind
set_option autoImplicit false
noncomputable section
namespace NIY_GammaReadPort
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport NIL_ResultReverse AspisR1
open NID_ResumeEmission

theorem source (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 (state a3 a4 : Array U8 32#usize) (r2 : verifier.Reader) :
 NIL_StatePort.reply (NIY_FirstRawCut.freshAfterRaw reserved d bytes v end1 i4 state a3 a4 r2)=
 NIY_CohortRawCut.afterRaw (CheckpointBytes4Ops.ops reserved) bytes (variant v) end1 i4 state a3 a4 (reader r2) := by
 with_unfolding_all rw [NIY_FirstECut.source,NIY_C_FirstECut.source]
 unfold NIL_StatePort.reply NIL_FreshOps.readE
 apply NIL_PortBind.read unE unReader NIL_StatePort.pair
 intro value out
 have h := NIY_KappaReadPort.source reserved d bytes v end1 i4 state a3 a4 (unE value) (unReader out)
 simpa only [NIL_StatePort.reply,e_reverse,reader_reverse] using h
#print axioms source
end NIY_GammaReadPort
