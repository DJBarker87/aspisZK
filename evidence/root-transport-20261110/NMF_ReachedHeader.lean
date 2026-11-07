import NLW_ReaderHeader
import RPz7_Cons_Native
set_option autoImplicit false
noncomputable section
namespace NMF_ReachedHeader
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- The actual reached resume comparison, with the original partial digest
and its accepted value law. The comparison is hash equality, never injectivity. -/
theorem returned {F C X : Type} (base : VTop_Stages.Ops)
 (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
 (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
 (D : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
 (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest D) hash H)
 (pub proof ck : Slice U8) (t : Cons_Native.Witness)
 (calls : Cons_Native.Calls base finish reserved query geo D hash pub proof ck t) :
 NLW_ReaderHeader.decode (MultiproofConeCanonical.bytesOf ck.val)=
 some (H (MultiproofConeCanonical.bytesOf proof.val),H (MultiproofConeCanonical.bytesOf pub.val)) := by
 have resumed:=Tx2N_Install.reader_success base reserved query D hash ck proof pub .S2 t.p2 t.saved2 calls.1
 obtain ⟨compared⟩:=CheckpointBytes4Comparison.successful_calls reserved
   (VTop_Checkpoint.digest D) ck proof pub .S2 hash t.p2 t.saved2 resumed
 exact NLW_ReaderHeader.calls (VTop_Checkpoint.digest D) hash H oracle ck proof pub compared calls.2.2.1
#print returned
#print axioms returned
end NMF_ReachedHeader
