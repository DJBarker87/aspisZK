import CurrentFinishField
import S3GroupedPairFinishInputCanonicalCurrent
import S3GroupedPairRealAddBodyCurrent

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1GroupedPairCut.Proofs.FinishCoeffArray

abbrev S := AspisR1GroupedPairCut.field.WideExact

theorem canonicalInputArray_of_finishField
    (bytes : Slice U8) (coeff : Array S 64#usize)
    (fieldIndex : Fin 64 → Usize)
    (hentry : ∀ j : Fin 64,
      ∃ x : AspisR1CurrentWide.Proof.FinishE,
        AspisR1CurrentWide.Proof.finishField bytes (fieldIndex j) = .ok x ∧
        coeff.val[j.val]'(by
          have hp := coeff.property
          change coeff.val.length = 64 at hp
          omega) =
          AspisR1GroupedPairCut.Proofs.FinishInputCanonicalCurrent.finishToS x) :
    AspisR1GroupedPairCut.Proofs.RealAddCurrent.CanonicalInputArray coeff := by
  intro j
  obtain ⟨x,hfield,hvalue⟩ := hentry j
  rw [hvalue]
  exact AspisR1GroupedPairCut.Proofs.FinishInputCanonicalCurrent.finishField_s3_canonical
    bytes (fieldIndex j) x hfield

end AspisR1GroupedPairCut.Proofs.FinishCoeffArray

#print axioms AspisR1GroupedPairCut.Proofs.FinishCoeffArray.canonicalInputArray_of_finishField
