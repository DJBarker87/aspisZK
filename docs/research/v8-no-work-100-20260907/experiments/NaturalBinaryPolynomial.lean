import AspisFormal.V5FriInitialCircleEncoderIdentity

/-! Polynomial, rather than point-evaluation, form of the maintained natural
binary split. The source recurrence is evaluated in K[X] and transported by
the composition ring homomorphism. No infinite-field assumption or finite
evaluation-to-polynomial shortcut is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 100000
namespace AspisV8.NaturalBinaryPolynomial
noncomputable section
open Polynomial AspisCircleTensorBinding AspisV5FriNaturalBasisRadix4
open AspisV5FriConcreteEncoderApplicability AspisV5FriInitialCircleEncoderIdentity

section Ring
variable {K R S : Type*} [CommRing K] [CommRing R] [CommRing S]

theorem doubledFactor_hom (f : R →+* S) (x : R) (bit : Nat) :
    f (doubledFactor x bit)=doubledFactor (f x) bit := by
  induction bit with
  | zero => rfl
  | succ bit ih => simp only [doubledFactor,map_sub,map_mul,map_ofNat,map_pow,map_one,ih]

theorem naturalLineValue_hom (f : R →+* S) (x : R) (n : Nat) :
    f (naturalLineValue x n)=naturalLineValue (f x) n := by
  simp only [naturalLineValue,map_prod,doubledFactor_hom]

/-- The same repeated squaring recurrence, now in the polynomial ring. -/
theorem doubledFactor_X (bit : Nat) :
    doubledFactor (X : K[X]) bit=Chebyshev.T K (2^bit : Nat) := by
  induction bit with
  | zero => simp [doubledFactor]
  | succ bit ih =>
    rw [doubledFactor,ih,show (2^(bit+1):Nat)=2*2^bit by omega]
    change 2*(Chebyshev.T K (2^bit : Nat))^2-1=
      Chebyshev.T K ((2:Int)*(2^bit:Nat))
    rw [Chebyshev.T_mul,Chebyshev.T_two]
    simp

theorem naturalLineValue_X (n : Nat) :
    naturalLineValue (X : K[X]) n=naturalLinePoly K n := by
  simp only [naturalLineValue,naturalLinePoly,doubledFactor_X]

theorem naturalLineValue_polynomial (p : K[X]) (n : Nat) :
    naturalLineValue p n=(naturalLinePoly K n).comp p := by
  have h:=naturalLineValue_hom (Polynomial.compRingHom p) (X : K[X]) n
  simpa only [Polynomial.coe_compRingHom_apply,Polynomial.X_comp,naturalLineValue_X] using h.symm

theorem basis_two_mul (n : Nat) :
    naturalLinePoly K (2*n)=(naturalLinePoly K n).comp (2*X^2-1) := by
  rw [←naturalLineValue_X,naturalLineValue_two_mul,naturalLineValue_polynomial]
  rfl

theorem basis_two_mul_add_one (n : Nat) :
    naturalLinePoly K (2*n+1)=X*(naturalLinePoly K n).comp (2*X^2-1) := by
  rw [←naturalLineValue_X,naturalLineValue_two_mul_add_one,naturalLineValue_polynomial]
  rfl
end Ring

section Field
variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- Exact MSB-independent low-bit split of the natural coefficient vector.
This is a polynomial identity over finite fields as well as infinite ones. -/
theorem binary_polynomial {n : Nat} (hn : 0<n) (c : Fin (2*n) → K) :
    naturalCoefficientPolynomial c=
      (naturalCoefficientPolynomial (evenCoefficients c)).comp (2*X^2-1)+
        X*(naturalCoefficientPolynomial (oddCoefficients c)).comp (2*X^2-1) := by
  rw [naturalCoefficientPolynomial_eq_basisSum (by omega),
    naturalCoefficientPolynomial_eq_basisSum hn,naturalCoefficientPolynomial_eq_basisSum hn]
  rw [←(binaryIndexEquiv n).sum_comp,Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two,binaryIndexEquiv_apply,binaryChildIndex,
    evenCoefficients,oddCoefficients,Fin.val_zero,Fin.val_one,add_zero]
  simp_rw [basis_two_mul,basis_two_mul_add_one]
  simp only [sum_comp,mul_comp,C_comp,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem initialP0_polynomial_lanes (c : Fin 1024 → K) :
    initialP0 c=
      (naturalCoefficientPolynomial
        (AspisV5ComponentCConcreteFoldLinearity.coefficientLane 256 0 c)).comp (2*X^2-1)+
      X*(naturalCoefficientPolynomial
        (AspisV5ComponentCConcreteFoldLinearity.coefficientLane 256 2 c)).comp (2*X^2-1) := by
  rw [initialP0,binary_polynomial (n:=256) (by decide)]
  rfl

theorem initialP1_polynomial_lanes (c : Fin 1024 → K) :
    initialP1 c=
      (naturalCoefficientPolynomial
        (AspisV5ComponentCConcreteFoldLinearity.coefficientLane 256 1 c)).comp (2*X^2-1)+
      X*(naturalCoefficientPolynomial
        (AspisV5ComponentCConcreteFoldLinearity.coefficientLane 256 3 c)).comp (2*X^2-1) := by
  rw [initialP1,binary_polynomial (n:=256) (by decide)]
  rfl

/-- Undo the explicit x²-to-T2 affine substitution, without dividing by a
polynomial or assuming any leading coefficient of the chord norm. -/
theorem affine_radial_roundtrip (p : K[X]) :
    (p.comp (C ((2:K)⁻¹)*(X+1))).comp (C 2*X-1)=p := by
  rw [comp_assoc]
  have affine : (C ((2:K)⁻¹)*(X+1)).comp (C 2*X-1)=(X : K[X]) := by
    simp only [mul_comp,C_comp,add_comp,X_comp,one_comp,sub_add_cancel]
    rw [←mul_assoc,←C_mul,inv_mul_cancel₀ (NeZero.ne (2:K)),C_1,one_mul]
  rw [affine,comp_X]

theorem affine_radial_square (p : K[X]) :
    (p.comp (C ((2:K)⁻¹)*(X+1))).comp (2*X^2-1)=p.comp (X^2) := by
  rw [comp_assoc]
  have affine : (C ((2:K)⁻¹)*(X+1)).comp (2*X^2-1)=(X^2 : K[X]) := by
    simp only [mul_comp,C_comp,add_comp,X_comp,one_comp,sub_add_cancel]
    rw [show (2:K[X])=C (2:K) by simp,←mul_assoc,←C_mul,
      inv_mul_cancel₀ (NeZero.ne (2:K)),C_1,one_mul]
  rw [affine]
end Field

#print axioms doubledFactor_hom
#print axioms naturalLineValue_hom
#print axioms doubledFactor_X
#print axioms naturalLineValue_polynomial
#print axioms basis_two_mul
#print axioms basis_two_mul_add_one
#print axioms binary_polynomial
#print axioms initialP0_polynomial_lanes
#print axioms initialP1_polynomial_lanes
#print axioms affine_radial_roundtrip
#print axioms affine_radial_square
end
end AspisV8.NaturalBinaryPolynomial
