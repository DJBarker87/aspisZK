import AspisV8R19.R738JointObservationModel
import AspisV8R19.FullCoefficientBoundary

/-! Finite coefficient-row evaluation for the same sparse pair directions as
R738.  This is a commutative-ring identity only. -/
set_option autoImplicit false
namespace AspisV8R19.R741SparseCoefficientObservation
open AspisR19 AspisR19.BetaUniformCorrection AspisR19.FullCoefficientBoundary
open AspisV8R19.R738JointObservationModel
open scoped BigOperators
noncomputable section
variable {F : Type*} [CommRing F]

def indexedBasis (n : Nat) (d : Fin n) (slot : Fin 4) : Fin n × Fin 4 → F :=
  fun i => if i=(d,slot) then 1 else 0

def indexedPair (alpha : F) (d : Fin 256) (s : Fin 3) : Fin 256 × Fin 4 → F :=
  indexedBasis 256 d ⟨s.val+1,by omega⟩ -
    alpha^(s.val+1) • indexedBasis 256 d 0

def rowWeight (k : Nat) (quarter : F) (w : Fin 256 × Fin 4 → F)
    (d : Fin 256) (slot : Fin 4) : F :=
  ∑ t : Fin 4, (if slot.val+(4-t.val)%4=k then quarter else 0)*w (d,t)

theorem coefficient_indexedBasis (n k : Nat) (quarter : F)
    (w : Fin n × Fin 4 → F) (d : Fin n) (slot : Fin 4) :
    coefficient (sourceKernel n k quarter) (indexedBasis n d slot) w =
      rowWeight k quarter w d slot := by
  rw [coefficient_blocks]
  simp [indexedBasis,rowWeight,Finset.sum_ite_eq',mul_assoc]

theorem coefficient_indexedPair (alpha : F) (k : Nat) (quarter : F)
    (w : Fin 256 × Fin 4 → F) (d : Fin 256) (s : Fin 3) :
    coefficient (sourceKernel 256 k quarter) (indexedPair alpha d s) w =
      rowWeight k quarter w d ⟨s.val+1,by omega⟩-
        alpha^(s.val+1)*rowWeight k quarter w d 0 := by
  rw [show indexedPair alpha d s =
      fun i => (1:F)*indexedBasis 256 d ⟨s.val+1,by omega⟩ i+
        (-alpha^(s.val+1))*indexedBasis 256 d 0 i by
      funext i; simp [indexedPair]; ring]
  rw [coefficient_left]
  simp only [one_mul,neg_mul]
  rw [coefficient_indexedBasis,coefficient_indexedBasis]
  ring

theorem coefficient_direction (alpha : F) (k : Nat) (quarter : F)
    (w : Fin 256 × Fin 4 → F) (d : Fin 256) (s : Fin 3) :
    coefficient (sourceKernel 256 k quarter)
      (fun i => indexedPair alpha d s i-indexedPair alpha 0 s i) w =
      (rowWeight k quarter w d ⟨s.val+1,by omega⟩-
        alpha^(s.val+1)*rowWeight k quarter w d 0)-
      (rowWeight k quarter w 0 ⟨s.val+1,by omega⟩-
        alpha^(s.val+1)*rowWeight k quarter w 0 0) := by
  rw [show (fun i => indexedPair alpha d s i-indexedPair alpha 0 s i) =
      fun i => (1:F)*indexedPair alpha d s i+(-1)*indexedPair alpha 0 s i by
      funext i; ring]
  rw [coefficient_left]
  simp only [one_mul,neg_mul]
  rw [coefficient_indexedPair,coefficient_indexedPair]
  ring

def cast255 (d : Fin 255) : Fin 256 := ⟨d.val,by omega⟩

theorem indexedPair_qPair (alpha : F) (d : Fin 255) (s : Fin 3)
    (i : Fin 256 × Fin 4) :
    indexedPair alpha (cast255 d) s i =
      qPair alpha d s (4*i.1.val+i.2.val) := by
  have hslot : ∀ (e : Fin 256) (u : Fin 4),
      (4*i.1.val+i.2.val = 4*e.val+u.val) ↔ i=(e,u) := by
    intro e u
    constructor
    · intro h
      apply Prod.ext <;> apply Fin.ext <;> dsimp only
      · omega
      · omega
    · intro h; subst i; rfl
  simp only [indexedPair,indexedBasis,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,qPair]
  rw [show (4*i.1.val+i.2.val = 4*(cast255 d).val+(s.val+1)) ↔
      i=(cast255 d,⟨s.val+1,by omega⟩) by exact hslot _ _,
    show (4*i.1.val+i.2.val = 4*(cast255 d).val) ↔ i=(cast255 d,0) by
      simpa using hslot (cast255 d) 0]
  simp [cast255]

#print axioms coefficient_indexedBasis
#print axioms coefficient_indexedPair
#print axioms coefficient_direction
#print axioms indexedPair_qPair
end
end AspisV8R19.R741SparseCoefficientObservation
