import NIY_GammaReadPort
import NIY_RawTransport
import NIY_CohortRawCut
set_option autoImplicit false
noncomputable section
namespace NIY_TailPort
open Aeneas Aeneas.Std Result NIL_Carriers AspisR1

/-- Exact fresh/cohort tail transport, obtained only by the typed continuation chain.
This is a source/model theorem, not an actual native caller packet. -/
theorem source (reserved : Bool) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8) (end1 : Usize) (next : U8) :
 NIL_StatePort.reply (NIL_ResumeSplit.tail reserved d bytes .S2 end1 next)=
 NIL_ResumeCohortTail.tail (CheckpointBytes4Ops.ops reserved) bytes .S2 end1 next := by
 with_unfolding_all rw [NIY_FirstRawCut.fresh_source,NIY_CohortRawCut.source]
 unfold NIY_FirstRawCut.fresh NIY_CohortRawCut.first3 NIL_StatePort.reply
 apply NIY_RawTransport.first3
 intro state a3 a4 out
 have h := NIY_GammaReadPort.source reserved d bytes .S2 end1 next state a3 a4 (unReader out)
 simpa only [NIL_StatePort.reply,reader_reverse,NIL_Carriers.variant] using h
#print axioms source
end NIY_TailPort
