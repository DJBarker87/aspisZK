import RPu_FJb_RawConversion
import RPu_RawPoseidonRowField
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_RawValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (K Canon decode)
abbrev M := ExtractedMaskQM31Exact.M31Exact
def tuple (w : (Nat×Nat)×(Nat×Nat)) : K :=
  ⟨⟨(w.1.1 : M),(w.1.2 : M)⟩,⟨(w.2.1 : M),(w.2.2 : M)⟩⟩
/-- All native raw-limb reductions preserve the exact decoded field value. -/
theorem value (raw : Array U64 4#usize) (out : NQ)
    (run : state_only_poseidon.extension_from_raw_limbs raw=ok out) :
    Canon out ∧ decode out=RawPoseidonRowField.decodeWords
      (fun j=>(RawPoseidonExtensionWords.limbAt raw j).val) := by
  have oldrun : AspisR1SelectedMaskProbe.state_only_poseidon.extension_from_raw_limbs raw=ok (qm out) := by
    rw [←FJb_RawConversion.converted,run,FIv_Map.map_ok]
  obtain ⟨q,hq,hc,hw⟩ := RawPoseidonExtensionWords.extension_from_raw_limbs_words raw
  have he : q=qm out := Result.ok.inj (hq.symm.trans oldrun)
  subst q
  refine ⟨hc,?_⟩
  have hd := congrArg tuple hw
  change decode out=tuple _ at hd
  rw [hd]
  change RawPoseidonRowField.decodeWords
    (fun j=>(RawPoseidonExtensionWords.limbAt raw j).val % AspisV8R15.ExactTowerBase.P)=_
  exact RawPoseidonRowField.decodeWords_mod _
#print axioms value
end AspisR1.FJb_RawValue
end
