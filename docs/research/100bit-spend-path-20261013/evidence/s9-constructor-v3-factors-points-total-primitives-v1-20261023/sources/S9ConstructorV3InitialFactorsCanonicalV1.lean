import AspisR1S9ActualWeightsNewBoxNewV3.Funs
import S9ConstructorV3Loop2InnerCanonicalV1
import S9CandidateFoldMapPrimitivesV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3InitialFactorsCanonicalV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1

/-- Symbolic repeated-array lemma; no unrolling of the nested concrete factor
matrix is needed. A successful mapped read returns the mapped repeated value. -/
theorem repeated_mapped_reads
    {A B : Type} (f : A → B) (P : B → Prop) (n : Usize) (x : A)
    (hx : P (f x)) :
    ∀ (i : Usize) (v : B),
      Array.index_usize
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f (Array.repeat n x)) i = .ok v → P v := by
  intro i v hread
  have hi := index_success_bound
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f (Array.repeat n x)) i v hread
  have hopt : (Array.repeat n x)[i]? = some x := by
    simp only [Array.getElem?_Usize_eq, Array.repeat]
    simp [hi]
  have hrepeat : Array.index_usize (Array.repeat n x) i = .ok x := by
    unfold Array.index_usize
    rw [hopt]
  have hmap := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
    f (Array.repeat n x) i
  rw [hrepeat] at hmap
  have he : f x = v := Result.ok.inj (hmap.trans hread)
  exact he ▸ hx

theorem zero_canonical :
    CanQ (toProbeQ AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ZERO) := by
  change CanQ
    (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
      (AspisR1S9ConstructorV3QMMulCanonicalV1.toActualQM
        AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ZERO))
  simp only [AspisR1S9ActualQM31WrappingMapV1.toProbeQM,
    AspisR1S9ConstructorV3QMMulCanonicalV1.toActualQM,
    AspisR1S9ConstructorV3QMMulCanonicalV1.toActualCM,
    AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ZERO]
  constructor <;> constructor <;> decide

def initialFactors : Factors :=
  Array.repeat 5#usize (Array.repeat 5#usize
    (Array.repeat 4#usize AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ZERO))

/-- Three applications of the symbolic repetition lemma prove canonicality of
all successful reads of the actual constructor's complete zero-initial matrix. -/
theorem initial_factors_canonical : FactorsCanonical initialFactors := by
  have hcell : CellsCanonical (mapCells
      (Array.repeat 4#usize AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ZERO)) :=
    repeated_mapped_reads toProbeQ CanQ 4#usize
      AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ZERO zero_canonical
  have hrow : RowsCanonical (mapRow (Array.repeat 5#usize
      (Array.repeat 4#usize AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ZERO))) :=
    repeated_mapped_reads mapCells CellsCanonical 5#usize
      (Array.repeat 4#usize AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ZERO) hcell
  exact repeated_mapped_reads mapRow RowsCanonical 5#usize
    (Array.repeat 5#usize
      (Array.repeat 4#usize AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ZERO)) hrow

#print axioms repeated_mapped_reads
#print axioms initial_factors_canonical
end AspisR1S9ConstructorV3InitialFactorsCanonicalV1
