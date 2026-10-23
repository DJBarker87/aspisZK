import S3ActualLoop0WholePrefix
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1GroupedPairActualFieldOpsV3.NativeZeroReadbackReuseV1
open AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete

theorem zero_seed_canonical : Canonical field.WideExact.ZERO := by
  change AspisR1CurrentWide.Proof.CanonicalWide (toE field.WideExact.ZERO)
  norm_num [AspisR1CurrentWide.Proof.CanonicalWide,
    AspisR1CurrentWide.Proof.CanonicalQM,
    AspisR1CurrentWide.Proof.toQM,
    AspisR1CurrentWide.Proof.toCM,
    AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM,
    AspisR1.ExtractedCurrentQM31Tower.CurrentCanonicalQM,
    AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,
    AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
    AspisR1.ExtractedCurrentTowerAdd.P,
    AspisR1.ExtractedCurrentM31AddSub.P,
    AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.toE,
    AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.toQM,
    AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.toCM,
    field.WideExact.ZERO, field.QM31.ZERO]

theorem zero_seed_decode : decode field.WideExact.ZERO = 0 := by
  change AspisR1CurrentWide.Proof.decodeWide (toE field.WideExact.ZERO) = 0
  apply QuadraticAlgebra.ext
  all_goals apply QuadraticAlgebra.ext
  all_goals apply QuadraticAlgebra.ext
  all_goals norm_num [AspisR1CurrentWide.Proof.decodeWide,
    AspisR1CurrentWide.Proof.decodeQM,
    AspisR1.ExtractedCurrentQM31Exact.decode,
    AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.toE,
    AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.toQM,
    AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.toCM,
    AspisR1CurrentWide.Proof.toQM,
    AspisR1CurrentWide.Proof.toCM,
    field.WideExact.ZERO, field.QM31.ZERO]

theorem zero_seed_meaning :
    DecodedMeaning (Array.repeat 12#usize field.WideExact.ZERO)
      (fun _ : Fin 12 => 0) := by
  intro k
  change decode ((List.replicate 12 field.WideExact.ZERO)[k.val]'(by simpa using k.isLt)) = 0
  rw [List.getElem_replicate]
  exact zero_seed_decode


#print axioms zero_seed_canonical
#print axioms zero_seed_decode
#print axioms zero_seed_meaning
end AspisR1GroupedPairActualFieldOpsV3.NativeZeroReadbackReuseV1
