import CheckpointBytes5Inputs
import CheckpointBytes4Comparison
import AdapterRwRanges
import NLW_WriterPair
set_option autoImplicit false
noncomputable section
namespace NLW_ReaderHeader
open Aeneas Aeneas.Std AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft AspisR1Stage2
/-- Concrete header decoder shared by the source writer and reader. -/
def decode (cp : Bytes) : Option (State × State) := do
 let proof ← SemanticRecordCodec.decodeState (slice cp 16 32)
 let pub ← SemanticRecordCodec.decodeState (slice cp 48 32)
 pure (proof,pub)
/-- The successful reader's actual comparison records bind the stored header
 to its actual digest inputs. Partial digest implementations remain partial. -/
theorem calls {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
 (H : Bytes → State) (oracle : CheckpointBytes5Inputs.Oracle D hash H)
 (ck proof pub : Slice U8) (c : AspisR1Stage2.Tx2ResumeDigests.Calls D hash ck proof pub)
 (length : ck.val.length=1768) :
 decode (bytesOf ck.val)=some (H (bytesOf proof.val),H (bytesOf pub.val)) := by
 have pf:=AdapterRw.Ranges.selected_exact ck c.storedProof 16#usize 48#usize
  (by decide) (by change 48≤ck.val.length; omega) c.proofField
 have pu:=AdapterRw.Ranges.selected_exact ck c.storedPublic 48#usize 80#usize
  (by decide) (by change 80≤ck.val.length; omega) c.publicField
 have v16 : (16#usize).val=16 := by scalar_tac
 have v48 : (48#usize).val=48 := by scalar_tac
 have v80 : (80#usize).val=80 := by scalar_tac
 have pfBytes : c.storedProof.val=(ck.val.drop 16).take 32 := by
  simpa only [v16,v48,v80] using pf.1
 have puBytes : c.storedPublic.val=(ck.val.drop 48).take 32 := by
  simpa only [v16,v48,v80] using pu.1
 have pp:= (CheckpointBytes5Inputs.calls_inputs D hash ck proof pub c length).1
 have up:= (CheckpointBytes5Inputs.calls_inputs D hash ck proof pub c length).2.1
 have hp : SemanticRecordCodec.decodeState (slice (bytesOf ck.val) 16 32)=
  some (H (bytesOf proof.val)) := by
  rw [←NLW_WriterPair.map_slice,←pfBytes,c.proofEqual,
   ←CheckpointBytesDigest.bytes_stateOf,SemanticRecordCodec.decodeState_bytes]
  rw [oracle _ _ c.proofCall,pp]
 have hu : SemanticRecordCodec.decodeState (slice (bytesOf ck.val) 48 32)=
  some (H (bytesOf pub.val)) := by
  rw [←NLW_WriterPair.map_slice,←puBytes,c.publicEqual,
   ←CheckpointBytesDigest.bytes_stateOf,SemanticRecordCodec.decodeState_bytes]
  rw [oracle _ _ c.publicCall,up]
 simp only [decode,hp,hu,Option.bind_some]
 rfl
#print decode
#print calls
#print axioms calls
end NLW_ReaderHeader
