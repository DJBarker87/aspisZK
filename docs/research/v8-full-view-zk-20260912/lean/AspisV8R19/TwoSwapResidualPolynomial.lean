import AspisV8R19.TwoSwapResidualSource

/-! Fourteen challenge coordinates are active. Fin 36 reuses the retained
degree interface; coordinates 14..35 do not supply the query roots here. -/
namespace AspisR19.TwoSwapResidualPolynomial
open MvPolynomial
noncomputable section
variable {F : Type*} [CommRing F]
abbrev Poly := MvPolynomial (Fin 36) F

def normalizedMatrix (half quarter kappa alpha u v : F) (z : Fin 10 → F)
    (sectionValues : Fin 13 → Fin 32 → F) : Matrix (Fin 13) (Fin 13) F :=
  TwoSwapResidualModel.matrix half quarter (1+u*v) (u*v-1) (-(u+v)) kappa alpha z sectionValues

def polynomial (half quarter : F) (sectionValues : Fin 13 → Fin 32 → F) :
    Matrix (Fin 13) (Fin 13) (Poly (F:=F)) :=
  normalizedMatrix (C half) (C quarter) (X 10) (X 11) (X 12) (X 13)
    (fun i => X ⟨i.val,by omega⟩) (fun j i => C (sectionValues j i))

def assigned (half quarter : F) (sectionValues : Fin 13 → Fin 32 → F) (s : Fin 36 → F) :
    Matrix (Fin 13) (Fin 13) F :=
  normalizedMatrix half quarter (s 10) (s 11) (s 12) (s 13)
    (fun i => s ⟨i.val,by omega⟩) sectionValues

theorem entry_evaluation (half quarter : F) (sectionValues : Fin 13 → Fin 32 → F)
    (s : Fin 36 → F) (i j : Fin 13) :
    eval s (polynomial half quarter sectionValues i j)=assigned half quarter sectionValues s i j := by
  unfold polynomial assigned normalizedMatrix
  rw [TwoSwapResidualModel.map_matrix]
  simp only [eval_C,eval_X,map_add,map_sub,map_mul,map_neg,map_one]

theorem determinant_evaluation (half quarter : F) (sectionValues : Fin 13 → Fin 32 → F)
    (s : Fin 36 → F) :
    eval s (polynomial half quarter sectionValues).det=(assigned half quarter sectionValues s).det := by
  rw [(eval s).map_det]
  congr 1
  ext i j
  exact entry_evaluation half quarter sectionValues s i j

theorem unused_coordinates (half quarter : F) (sectionValues : Fin 13 → Fin 32 → F)
    (s t : Fin 36 → F) (h : ∀ i, i.val<14 → s i=t i) :
    assigned half quarter sectionValues s=assigned half quarter sectionValues t := by
  unfold assigned
  rw [h 10 (by decide),h 11 (by decide),h 12 (by decide),h 13 (by decide)]
  have hz : (fun i : Fin 10 => s ⟨i.val,by omega⟩)=(fun i : Fin 10 => t ⟨i.val,by omega⟩) := by
    funext i
    exact h ⟨i.val,by omega⟩ (by change i.val<14; omega)
  rw [hz]

section Field
variable {K : Type*} [Field K] [NeZero (2 : K)]

theorem source_evaluation (half quarter tau : K) (previous : Fin 271 → K)
    (t : Fin 22 → K) (ht : Function.Injective t) (noneOne : ∀ i, t i≠1) (s : Fin 36 → K) :
    eval s (polynomial half quarter (TwoSwapResidualSource.querySection t ht noneOne)).det=
      (TwoSwapResidualSource.matrix half quarter (1+s 12*s 13) (s 12*s 13-1) (-(s 12+s 13))
        (s 10) (s 11) tau (fun i => s ⟨i.val,by omega⟩) previous t ht noneOne).det := by
  rw [determinant_evaluation,TwoSwapResidualSource.matrix_eq _ _ _ _ _ _ _ _ _ _ _ ht noneOne]
  rfl
end Field

#print axioms entry_evaluation
#print axioms determinant_evaluation
#print axioms unused_coordinates
#print axioms source_evaluation
end
end AspisR19.TwoSwapResidualPolynomial
