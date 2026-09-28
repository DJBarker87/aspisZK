/- Root construction and normalized chord substituted before any nonvanishing
   claim. No independent-uniform sampler or negligible-loss premise. -/
import AspisV8R19.ResidualHomogeneous

namespace AspisR19.SourceResidualPolynomial
open MvPolynomial ResidualModel ResidualPins
variable {F : Type*} [CommRing F]
noncomputable section

def rootRun (half : F) : List F → (Fin 27 → F) → Fin 27 → F
  | [],p => p
  | r::roots,p => rootRun half roots (fun j => shift half 1 p j-r*p j)
def rootCoefficients (half : F) (roots : Fin 22 → F) (r : Fin 23) : F :=
  rootRun half (List.ofFn roots) (fun j => if j.val=0 then 1 else 0) ⟨r.val,by omega⟩

theorem map_rootRun {G : Type*} [CommRing G] (f : F →+* G) (half : F)
    (roots : List F) (p : Fin 27 → F) (j : Fin 27) :
    f (rootRun half roots p j)=rootRun (f half) (roots.map f) (fun i => f (p i)) j := by
  induction roots generalizing p with
  | nil => rfl
  | cons r roots ih =>
      simp only [rootRun,List.map_cons,ih,map_sub,map_mul,map_shift]

theorem map_rootCoefficients {G : Type*} [CommRing G] (f : F →+* G)
    (half : F) (roots : Fin 22 → F) (r : Fin 23) :
    f (rootCoefficients half roots r)=rootCoefficients (f half) (fun i => f (roots i)) r := by
  unfold rootCoefficients
  rw [map_rootRun]
  simp [apply_ite]

def normalizedMinor (half quarter κ alpha u v : F) (z : Fin 10 → F)
    (roots : Fin 22 → F) : Matrix (Fin 13) (Fin 13) F :=
  minor order inactive half quarter (1+u*v) (u*v-1) (-(u+v)) κ alpha z
    (rootCoefficients half roots)

/- 0..9=z, 10=kappa, 11=alpha, 12=u, 13=v, 14..35=query roots. -/
def polyMinor (half quarter : F) : Matrix (Fin 13) (Fin 13) (MvPolynomial (Fin 36) F) :=
  normalizedMinor (C half) (C quarter) (X 10) (X 11) (X 12) (X 13)
    (fun i => X ⟨i.val,by omega⟩) (fun i => X ⟨14+i.val,by omega⟩)
def assignedMinor (half quarter : F) (s : Fin 36 → F) : Matrix (Fin 13) (Fin 13) F :=
  normalizedMinor half quarter (s 10) (s 11) (s 12) (s 13)
    (fun i => s ⟨i.val,by omega⟩) (fun i => s ⟨14+i.val,by omega⟩)

theorem entry_evaluation (half quarter : F) (s : Fin 36 → F) (i j : Fin 13) :
    eval s (polyMinor half quarter i j)=assignedMinor half quarter s i j := by
  unfold polyMinor assignedMinor normalizedMinor minor
  rw [map_observation]
  simp only [map_rootCoefficients,map_add,map_mul,map_sub,map_neg,map_one,eval_C,eval_X]

theorem determinant_evaluation (half quarter : F) (s : Fin 36 → F) :
    eval s (polyMinor half quarter).det=(assignedMinor half quarter s).det := by
  rw [(eval s).map_det]
  congr 1
  ext i j
  exact entry_evaluation half quarter s i j

theorem rational_nonzero_iff {K : Type*} [Field K]
    (half quarter κ alpha u v : K) (z : Fin 10 → K) (roots : Fin 22 → K)
    (h2 : (2:K)≠0) (hu : 1+u^2≠0) (hv : 1+v^2≠0) (hne : v≠u) :
    (minor order inactive half quarter
      (AspisV8R17.rationalX u*AspisV8R17.rationalY v-
        AspisV8R17.rationalY u*AspisV8R17.rationalX v)
      (AspisV8R17.rationalY u-AspisV8R17.rationalY v)
      (AspisV8R17.rationalX v-AspisV8R17.rationalX u)
      κ alpha z (rootCoefficients half roots)).det≠0 ↔
      (normalizedMinor half quarter κ alpha u v z roots).det≠0 := by
  rw [ResidualHomogeneous.rational_determinant half quarter κ alpha u v z
    (rootCoefficients half roots) hu hv]
  have hs := AspisV8R17.chordScale_ne_zero u v h2 hu hv hne
  simp [normalizedMinor,hs]

#print axioms map_rootRun
#print axioms map_rootCoefficients
#print axioms entry_evaluation
#print axioms determinant_evaluation
#print axioms rational_nonzero_iff
end
end AspisR19.SourceResidualPolynomial
