import LIBB_PoolLib
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryByteCut
open Aeneas Aeneas.Std

def empty : Slice U8 := ⟨[],by simp⟩

theorem registry1_nil : LIBB_PoolLib.library.decodeRegistryV1 [] = none := by
 have h := LIBB_V1DecoderValues.registry_result empty
 change Result.ok (none : Option RSL.RegistryV1) = Result.ok (LIBB_PoolLib.library.decodeRegistryV1 []) at h
 exact (Result.ok.inj h).symm

theorem entry1_nil : LIBB_PoolLib.library.decodeEntryV1 [] = none := by
 have h := LIBB_V1DecoderValues.entry_result empty
 change Result.ok (none : Option RSL.EntryV1) = Result.ok (LIBB_PoolLib.library.decodeEntryV1 []) at h
 exact (Result.ok.inj h).symm

theorem registry2_nil : LIBB_PoolLib.library.decodeRegistryV2 [] = none := by
 have h := LIBB_V2DecoderValues.registry_result empty
 unfold NCX_Install.op33 at h
 rw [NHY_RegistryModel.source] at h
 change Result.ok (none : Option RSL.RegistryV2) = Result.ok (LIBB_PoolLib.library.decodeRegistryV2 []) at h
 exact (Result.ok.inj h).symm

theorem entry2_nil : LIBB_PoolLib.library.decodeEntryV2 [] = none := by
 have h := LIBB_V2DecoderValues.entry_result empty
 unfold NCX_Install.op34 at h
 rw [NIJ_EntryModel.source] at h
 change Result.ok (none : Option RSL.EntryV2) = Result.ok (LIBB_PoolLib.library.decodeEntryV2 []) at h
 exact (Result.ok.inj h).symm

/-- Only a mathematical, unrepresentable oversized payload is cut. Each
supplied decoder rejects it and the empty payload before reading a field. -/
def cut (b : RSL.Bytes) : RSL.Bytes := if b.length ≤ Usize.max then b else []

theorem bound (b : RSL.Bytes) : (cut b).length ≤ Usize.max := by
 unfold cut
 split
 · assumption
 · exact Nat.zero_le _

theorem registry1 (b : RSL.Bytes) :
 LIBB_PoolLib.library.decodeRegistryV1 (cut b) = LIBB_PoolLib.library.decodeRegistryV1 b := by
 unfold cut
 split
 · rfl
 · rename_i large
   rw [registry1_nil]
   change none = LIBB_V1DecoderValues.registry b
   simp only [LIBB_V1DecoderValues.registry,dif_neg large]

theorem entry1 (b : RSL.Bytes) :
 LIBB_PoolLib.library.decodeEntryV1 (cut b) = LIBB_PoolLib.library.decodeEntryV1 b := by
 unfold cut
 split
 · rfl
 · rename_i large
   rw [entry1_nil]
   change none = LIBB_V1DecoderValues.entry b
   simp only [LIBB_V1DecoderValues.entry,dif_neg large]

theorem registry2 (b : RSL.Bytes) :
 LIBB_PoolLib.library.decodeRegistryV2 (cut b) = LIBB_PoolLib.library.decodeRegistryV2 b := by
 unfold cut
 split
 · rfl
 · rename_i large
   rw [registry2_nil]
   change none = LIBB_V2DecoderValues.registry b
   simp only [LIBB_V2DecoderValues.registry,dif_neg large]

theorem entry2 (b : RSL.Bytes) :
 LIBB_PoolLib.library.decodeEntryV2 (cut b) = LIBB_PoolLib.library.decodeEntryV2 b := by
 unfold cut
 split
 · rfl
 · rename_i large
   rw [entry2_nil]
   change none = LIBB_V2DecoderValues.entry b
   simp only [LIBB_V2DecoderValues.entry,dif_neg large]

#print axioms registry1_nil
#print axioms entry1_nil
#print axioms registry2_nil
#print axioms entry2_nil
#print axioms bound
#print axioms registry1
#print axioms entry1
#print axioms registry2
#print axioms entry2
end NMX_R3_RegistryByteCut
end
