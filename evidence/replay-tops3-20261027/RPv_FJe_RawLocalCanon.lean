import RPv_FJb_RawConversion
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_RawLocalCanon
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (Canon)
/-- Successful original raw conversion is canonical for arbitrary raw limbs;
this reuses the predecessor's checked unrestricted reducer. -/
theorem converted (xs : Array U64 4#usize) (out : NQ)
    (run : state_only_poseidon.extension_from_raw_limbs xs=ok out) : Canon out := by
  have oldRun := FJb_RawConversion.converted xs
  rw [run,FIv_Map.map_ok] at oldRun
  obtain ⟨q,hq,hc,_⟩ := RawPoseidonExtensionWords.extension_from_raw_limbs_words xs
  have same : q=qm out := Result.ok.inj (hq.symm.trans oldRun.symm)
  rw [same] at hc
  exact hc
/-- This local output bound is derived on the SAME original helper result;
it is not an assumed value for the complete external layer. -/
theorem local_value (input : Array NQ 4#usize) (out : NQ)
    (run : state_only_poseidon.external_local_packed input=ok out) : Canon out := by
  unfold state_only_poseidon.external_local_packed at run
  obtain ⟨raw,_,tail⟩ := FIv_Map.bind_success _ _ _ run
  exact converted raw out tail
#print axioms converted
#print axioms local_value
end AspisR1.FJe_RawLocalCanon
end
