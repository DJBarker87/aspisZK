import RPu_FJe_PackedRawValue
import RPu_FJe_RawConversionValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_LocalPackedValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical decoded)
open FJb_TailCell (cell)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
open AspisV8R15.ExactTowerBase (P)
/-- Complete actual local packed helper VALUE and canonicality. This composes
the exact checked source suffix with the closed form used by the P6 reference. -/
theorem value (input : Array NQ 4#usize) (out : NQ) (hc : canonical input)
    (run : state_only_poseidon.external_local_packed input=ok out) :
    Canon out ∧ decode out=R0P.poseidonPackingFormula iBasis uBasis
      (R0P.poseidonMat4 (decoded input)) := by
  unfold state_only_poseidon.external_local_packed at run
  obtain ⟨raw,hr,tail⟩ := FIv_Map.bind_success _ _ _ run
  have vr := FJe_PackedRawValue.value input raw hc hr
  have vc := FJe_RawConversionValue.value raw out tail
  have er : (fun j=>(RawPoseidonExtensionWords.limbAt raw j).val)=
      PoseidonExternalPackedAlgebra.packedNat (7*P) (FJe_PackedRawValue.matrix input) :=
    funext vr
  have wordModel : (fun r=>RawPoseidonRowField.decodeWords
      (FJe_PackedRawRowValue.words (FJe_PackedInputWords.mapped input) r))=decoded input := by
    funext r
    exact FJe_PackedInputWords.decoded_value input r
  have vf := FJe_RawReference.value
    (FJe_PackedRawRowValue.words (FJe_PackedInputWords.mapped input))
    (FJe_PackedInputWords.bounded input hc)
  refine ⟨vc.1,vc.2.trans ?_⟩
  rw [er]
  exact vf.trans (congrArg (fun f=>R0P.poseidonPackingFormula iBasis uBasis
    (R0P.poseidonMat4 f)) wordModel)
#print axioms value
end AspisR1.FJe_LocalPackedValue
end
