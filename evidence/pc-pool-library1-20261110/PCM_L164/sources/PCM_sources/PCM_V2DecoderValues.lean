import PCM_V2DecoderTotal
import PCM_V1DecoderValues
import PCM_Bytes
import NND_EntryV2Carrier
set_option autoImplicit false
noncomputable section
namespace PCM_V2DecoderValues
open Aeneas Aeneas.Std Result NND_Carrier PCM_ResultTotal PCM_Bytes

open PCM_V1DecoderValues (asOption)

/-- The source consumers map every format Err to InvalidAccountData, so only
at that call boundary is the Option projection used. No decoder Err is
claimed equal to another constructor. Unrepresentable RSL byte lists reject. -/
def registry (bs : RSL.Bytes) : Option RSL.RegistryV2 :=
 if h : bs.length ≤ Usize.max then
  asOption registryV2 (value (NCX_Install.op33 (fromBytes bs h)) (PCM_V2DecoderTotal.registry _))
 else none

def entry (bs : RSL.Bytes) : Option RSL.EntryV2 :=
 if h : bs.length ≤ Usize.max then
  asOption entryV2 (value (NCX_Install.op34 (fromBytes bs h)) (PCM_V2DecoderTotal.entry _))
 else none

theorem registry_bytes (b : Slice U8) : registry (PCM_Bytes.bytes b) =
 asOption registryV2 (value (NCX_Install.op33 b) (PCM_V2DecoderTotal.registry b)) := by
 unfold registry
 simp only [dif_pos (bytes_bound b),from_bytes]

theorem entry_bytes (b : Slice U8) : entry (PCM_Bytes.bytes b) =
 asOption entryV2 (value (NCX_Install.op34 b) (PCM_V2DecoderTotal.entry b)) := by
 unfold entry
 simp only [dif_pos (bytes_bound b),from_bytes]

theorem registry_result (b : Slice U8) :
 PCM_ResultTotal.mapOuter (asOption registryV2) (NCX_Install.op33 b) = ok (registry (PCM_Bytes.bytes b)) := by
 rw [equation _ (PCM_V2DecoderTotal.registry b),registry_bytes]
 rfl

theorem entry_result (b : Slice U8) :
 PCM_ResultTotal.mapOuter (asOption entryV2) (NCX_Install.op34 b) = ok (entry (PCM_Bytes.bytes b)) := by
 rw [equation _ (PCM_V2DecoderTotal.entry b),entry_bytes]
 rfl

#print axioms registry_bytes
#print axioms entry_bytes
#print axioms registry_result
#print axioms entry_result
end PCM_V2DecoderValues
end
