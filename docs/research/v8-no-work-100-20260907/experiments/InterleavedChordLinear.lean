import NaturalProjectionCore
import NaturalLineBoundary
import AspisFormal.V5FriInitialCircleEncoderIdentity

/-! Generic linear maps and literal low-bit interleaving, before the selected
1024-coordinate chord map is constructed. Reuses the maintained binary
coefficient index equivalence rather than an assumed encoder/basis map. -/
set_option autoImplicit false
set_option maxRecDepth 200
namespace AspisV8.InterleavedChordLinear
noncomputable section
open Polynomial Matrix AspisCircleTensorBinding
open AspisV5FriConcreteEncoderApplicability AspisV5FriInitialCircleEncoderIdentity
open AspisV8.NaturalChordImage AspisV8.NaturalChordProjection
variable {K : Type*} [Field K] [NeZero (2 : K)]

def coefficientLinear (m : Nat) : K[X] →ₗ[K] (Fin m → K) :=
  (monomialToNatural K m).mulVecLin.comp
    (LinearMap.pi (fun i : Fin m => Polynomial.lcoeff K i.val))

theorem coefficientLinear_apply (m : Nat) (p : K[X]) :
    coefficientLinear m p=coefficients m p := rfl

def projectLinear (n r : Nat) : K[X] →ₗ[K] (Fin n → K) :=
  LinearMap.pi (fun i : Fin n =>
    (LinearMap.proj (i.castAdd r)).comp (coefficientLinear (n+r)))

theorem projectLinear_apply (n r : Nat) (p : K[X]) :
    projectLinear n r p=projectLine n r p := rfl

def lineLinear (n : Nat) : (Fin n → K) →ₗ[K] K[X] where
  toFun := line
  map_add' v w := by
    simp only [line, Pi.add_apply, C_add, add_mul, Finset.sum_add_distrib]
  map_smul' s v := by
    simp only [line, Pi.smul_apply, smul_eq_mul, C_mul, Polynomial.smul_eq_C_mul,
      Finset.mul_sum, mul_assoc, RingHom.id_apply]

def evenLinear (n : Nat) : (Fin (2*n) → K) →ₗ[K] (Fin n → K) where
  toFun := evenCoefficients
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def oddLinear (n : Nat) : (Fin (2*n) → K) →ₗ[K] (Fin n → K) where
  toFun := oddCoefficients
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def interleave {n : Nat} (a b : Fin n → K) : Fin (2*n) → K :=
  fun i => if binarySlotIndex i=0 then a (binaryParentIndex i) else b (binaryParentIndex i)

@[simp] theorem interleave_even {n : Nat} (a b : Fin n → K) :
    evenCoefficients (interleave a b)=a := by
  funext j
  change interleave a b (binaryChildIndex j 0)=a j
  simp [interleave]

@[simp] theorem interleave_odd {n : Nat} (a b : Fin n → K) :
    oddCoefficients (interleave a b)=b := by
  funext j
  change interleave a b (binaryChildIndex j 1)=b j
  simp [interleave]

def interleaveLinear (n : Nat) :
    ((Fin n → K) × (Fin n → K)) →ₗ[K] (Fin (2*n) → K) where
  toFun p := interleave p.1 p.2
  map_add' p q := by
    funext i
    change interleave (p.1+q.1) (p.2+q.2) i=interleave p.1 p.2 i+interleave q.1 q.2 i
    unfold interleave
    split_ifs <;> rfl
  map_smul' s p := by
    funext i
    change interleave (s • p.1) (s • p.2) i=s*interleave p.1 p.2 i
    unfold interleave
    split_ifs <;> rfl

/-- Dot products split into the actual even/odd coefficient lanes. -/
theorem interleave_dot {n : Nat} (w : Fin (2*n) → K) (a b : Fin n → K) :
    (∑ i, w i*interleave a b i)=
      (∑ j, evenCoefficients w j*a j)+(∑ j, oddCoefficients w j*b j) := by
  rw [← (binaryIndexEquiv n).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, binaryIndexEquiv_apply, interleave,
    binaryParentIndex_childIndex, binarySlotIndex_childIndex, if_pos rfl]
  simp only [show (1:Fin 2) ≠ 0 by decide, if_false, Finset.sum_add_distrib]
  rfl

theorem line_polynomial {n : Nat} (hn : 0<n) (v : Fin n → K) :
    naturalCoefficientPolynomial v=line v := naturalCoefficientPolynomial_eq_basisSum hn v

#print axioms coefficientLinear_apply
#print axioms projectLinear_apply
#print axioms lineLinear
#print axioms interleave_even
#print axioms interleave_odd
#print axioms interleaveLinear
#print axioms interleave_dot
#print axioms line_polynomial
end
end AspisV8.InterleavedChordLinear
