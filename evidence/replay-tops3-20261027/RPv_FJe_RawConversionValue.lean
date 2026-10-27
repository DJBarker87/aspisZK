import RPv_FJe_RawLocalCanon
import RPv_RawPoseidonRowField
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_RawConversionValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ qm cm)
open FIv_NativeValue (Canon decode)
open RawPoseidonExtensionWords (limbAt)
/-- The actual raw conversion's COMPLETE decoded value,with no assumed
intermediate conversion result. -/
theorem value (xs : Array U64 4#usize) (out : NQ)
    (run : state_only_poseidon.extension_from_raw_limbs xs=ok out) :
    Canon out ∧ decode out=RawPoseidonRowField.decodeWords (fun j=>(limbAt xs j).val) := by
  have oldRun := FJb_RawConversion.converted xs
  rw [run,FIv_Map.map_ok] at oldRun
  obtain ⟨q,hq,hc,hw⟩ := RawPoseidonExtensionWords.extension_from_raw_limbs_words xs
  have same : q=qm out := Result.ok.inj (hq.symm.trans oldRun.symm)
  subst q
  have h0 := congrArg (fun w : (Nat×Nat)×(Nat×Nat)=>w.1.1) hw
  have h1 := congrArg (fun w : (Nat×Nat)×(Nat×Nat)=>w.1.2) hw
  have h2 := congrArg (fun w : (Nat×Nat)×(Nat×Nat)=>w.2.1) hw
  have h3 := congrArg (fun w : (Nat×Nat)×(Nat×Nat)=>w.2.2) hw
  change out.c0.a.val=(limbAt xs 0).val%ExtractedMaskTowerAdd.P at h0
  change out.c0.b.val=(limbAt xs 1).val%ExtractedMaskTowerAdd.P at h1
  change out.c1.a.val=(limbAt xs 2).val%ExtractedMaskTowerAdd.P at h2
  change out.c1.b.val=(limbAt xs 3).val%ExtractedMaskTowerAdd.P at h3
  have hd : decode out=RawPoseidonRowField.decodeWords
      (fun j=>(limbAt xs j).val%AspisV8R15.ExactTowerBase.P) := by
    ext <;> simp only [decode,ExtractedMaskQM31Exact.decode,qm,cm,
      RawPoseidonRowField.decodeWords,h0,h1,h2,h3]
  exact ⟨hc,hd.trans (RawPoseidonRowField.decodeWords_mod _)⟩
#print axioms value
end AspisR1.FJe_RawConversionValue
end
