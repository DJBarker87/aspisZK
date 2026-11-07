import PCM_V1DecoderTotal
import PCM_Bytes
import NND_EntryV2Carrier
set_option autoImplicit false
noncomputable section
namespace PCM_V1DecoderValues
open Aeneas Aeneas.Std Result NND_Carrier PCM_ResultTotal PCM_Bytes

def asOption {A B E : Type} (f : A → B) : core.result.Result A E → Option B
 | .Ok x => some (f x) | .Err _ => none

/-- The source consumers map every format Err to InvalidAccountData, so only
at that call boundary is the Option projection used. No decoder Err is
claimed equal to another constructor. Unrepresentable RSL byte lists reject. -/
def registry (bs : RSL.Bytes) : Option RSL.RegistryV1 :=
 if h : bs.length ≤ Usize.max then
  asOption registryV1 (value (NJQ_Canonical.registry (fromBytes bs h)) (PCM_V1DecoderTotal.registry _))
 else none

def entry (bs : RSL.Bytes) : Option RSL.EntryV1 :=
 if h : bs.length ≤ Usize.max then
  asOption entryV1 (value (NJQ_Canonical.entry (fromBytes bs h)) (PCM_V1DecoderTotal.entry _))
 else none

theorem registry_bytes (b : Slice U8) : registry (bytes b) =
 asOption registryV1 (value (NJQ_Canonical.registry b) (PCM_V1DecoderTotal.registry b)) := by
 unfold registry
 simp only [dif_pos (bytes_bound b),from_bytes]

theorem entry_bytes (b : Slice U8) : entry (bytes b) =
 asOption entryV1 (value (NJQ_Canonical.entry b) (PCM_V1DecoderTotal.entry b)) := by
 unfold entry
 simp only [dif_pos (bytes_bound b),from_bytes]

theorem registry_result (b : Slice U8) :
 PCM_ResultTotal.mapOuter (asOption registryV1) (NJQ_Canonical.registry b) = ok (registry (bytes b)) := by
 rw [equation _ (PCM_V1DecoderTotal.registry b),registry_bytes]
 rfl

theorem entry_result (b : Slice U8) :
 PCM_ResultTotal.mapOuter (asOption entryV1) (NJQ_Canonical.entry b) = ok (entry (bytes b)) := by
 rw [equation _ (PCM_V1DecoderTotal.entry b),entry_bytes]
 rfl

#print axioms registry_bytes
#print axioms entry_bytes
#print axioms registry_result
#print axioms entry_result
end PCM_V1DecoderValues
end
