import RPu_FJh_Base
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_RawLimbReassembly
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (QM Decode Canonical)
open RawPoseidonExtensionWords (Limbs limbAt)
open RawPoseidonRowField (decodeWords)
theorem source_success (xs : Limbs) :
    ∃ out : QM,state_only_poseidon.extension_from_raw_limbs xs=ok out ∧
      Canonical out ∧ Decode out=decodeWords (fun j=>(limbAt xs j).val) := by
  obtain ⟨q,hq,_⟩ := RawPoseidonExtensionWords.extension_from_raw_limbs_words xs
  have eq := FJb_RawConversion.converted xs
  rw [hq] at eq
  cases run : state_only_poseidon.extension_from_raw_limbs xs with
  | ok out => exact ⟨out,rfl,FJe_RawConversionValue.value xs out run⟩
  | fail e => rw [run] at eq;cases eq
  | div => rw [run] at eq;cases eq
#print axioms source_success
end AspisR1.FJh_RawLimbReassembly
end
