import AspisFormal.V5FriConcreteEncoderCommutation

/-! Exact denominator clearing in the low-bit [1,y,x,xy] circle fibre.
This constructs the numerator, rather than assuming a rational representation.
It is an algebraic interface for the wrong-OOD/polynomial-raw-word case,
not an arbitrary-oracle recovery theorem or a probability certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 100000
namespace AspisV8.ChordRationalAlgebra
open AspisV5FriConcreteEncoderCommutation
open AspisV5ComponentCConcreteFoldLinearity

section Ring
variable {R : Type*} [CommRing R]

def value (x y : R) (u : Fin 4 → R) : R :=
  u 0+y*u 1+x*u 2+x*y*u 3

def product (s t : R) (u v : Fin 4 → R) : Fin 4 → R :=
  ![u 0*v 0+t*u 1*v 1+s*u 2*v 2+s*t*u 3*v 3,
    u 0*v 1+u 1*v 0+s*(u 2*v 3+u 3*v 2),
    u 0*v 2+u 2*v 0+t*(u 1*v 3+u 3*v 1),
    u 0*v 3+u 3*v 0+u 1*v 2+u 2*v 1]

def line (a b c : R) : Fin 4 → R := ![a,c,b,0]
def adjugate (a b c s t : R) : Fin 4 → R :=
  ![a*(a^2-b^2*s-c^2*t),
    -c*(a^2+b^2*s-c^2*t),
    -b*(a^2-b^2*s+c^2*t),
    2*a*b*c]
def norm (a b c s t : R) : R :=
  (a^2+b^2*s-c^2*t)^2-4*a^2*b^2*s

theorem product_value (s t x y : R) (hx : x^2=s) (hy : y^2=t)
    (u v : Fin 4 → R) :
    value x y (product s t u v)=value x y u*value x y v := by
  dsimp [value,product]
  ring_nf
  simp only [hx,hy]
  ring

theorem line_adjugate (a b c s t : R) :
    product s t (line a b c) (adjugate a b c s t)=![norm a b c s t,0,0,0] := by
  funext j
  fin_cases j <;> simp [product,line,adjugate,norm] <;> ring

theorem line_value (a b c x y : R) :
    value x y (line a b c)=a+b*x+c*y := by
  simp [value,line]
  ring

theorem line_times_adjugate (a b c s t x y : R) (hx : x^2=s) (hy : y^2=t) :
    (a+b*x+c*y)*value x y (adjugate a b c s t)=norm a b c s t := by
  rw [←line_value,←product_value s t x y hx hy,line_adjugate]
  simp [value]

theorem norm_signed_product (a b c x y : R) :
    norm a b c (x^2) (y^2)=
      (a+b*x+c*y)*(a+b*x-c*y)*(a-b*x-c*y)*(a-b*x+c*y) := by
  unfold norm
  ring
end Ring

section Field
variable {K : Type*} [Field K]

def fibre (x y : K) (u : Fin 4 → K) : Fin 4 → K :=
  ![value x y u,value x (-y) u,value (-x) (-y) u,value (-x) y u]

theorem fibre_source (x y : K) (u : Fin 4 → K) :
    fibre x y u=radix4Evaluate y (-y) x u := by
  funext j
  fin_cases j <;> dsimp [fibre,value,radix4Evaluate] <;> ring

theorem local_division (a b c s t x y : K) (hx : x^2=s) (hy : y^2=t)
    (nonzero : norm a b c s t≠0) (u : Fin 4 → K) :
    value x y u/(a+b*x+c*y)=
      value x y (product s t u (adjugate a b c s t))/norm a b c s t := by
  have h := line_times_adjugate a b c s t x y hx hy
  have lineNonzero : a+b*x+c*y≠0 := by
    intro hz
    rw [hz,zero_mul] at h
    exact nonzero h.symm
  apply (div_eq_div_iff lineNonzero nonzero).mpr
  rw [product_value s t x y hx hy]
  calc
    value x y u*norm a b c s t=
        value x y u*((a+b*x+c*y)*value x y (adjugate a b c s t)) := by rw [h]
    _ = value x y u*value x y (adjugate a b c s t)*(a+b*x+c*y) := by ring

def quotientFibre (a b c x y : K) (u : Fin 4 → K) : Fin 4 → K :=
  ![value x y u/(a+b*x+c*y),value x (-y) u/(a+b*x-c*y),
    value (-x) (-y) u/(a-b*x-c*y),value (-x) y u/(a-b*x+c*y)]

theorem quotient_fibre_cleared (a b c x y : K) (u : Fin 4 → K)
    (nonzero : norm a b c (x^2) (y^2)≠0) :
    quotientFibre a b c x y u=
      (norm a b c (x^2) (y^2))⁻¹ •
        fibre x y (product (x^2) (y^2) u (adjugate a b c (x^2) (y^2))) := by
  have h (xx yy : K) (hx : xx^2=x^2) (hy : yy^2=y^2) :=
    local_division a b c (x^2) (y^2) xx yy hx hy nonzero u
  funext j
  fin_cases j <;> dsimp [quotientFibre,fibre]
  · simpa only [div_eq_mul_inv,mul_comm] using h x y rfl rfl
  · simpa only [mul_neg,sub_eq_add_neg,div_eq_mul_inv,mul_comm] using
      h x (-y) rfl (by ring)
  · simpa only [mul_neg,sub_eq_add_neg,div_eq_mul_inv,mul_comm] using
      h (-x) (-y) (by ring) (by ring)
  · simpa only [mul_neg,sub_eq_add_neg,div_eq_mul_inv,mul_comm] using
      h (-x) y (by ring) rfl

/-- The actual V7-consumed normalized circle fold, not an independently
chosen four-point map. Both base inverse equations are explicit inputs. -/
theorem normalized_fold_cleared (a b c x y alpha ix iy : K)
    (hx : 2*x*ix=1) (hy : 2*y*iy=1) (u : Fin 4 → K)
    (nonzero : norm a b c (x^2) (y^2)≠0) :
    circleFoldValue alpha ix iy (quotientFibre a b c x y u)=
      coefficientFoldValue alpha
        (product (x^2) (y^2) u (adjugate a b c (x^2) (y^2)))/
          norm a b c (x^2) (y^2) := by
  rw [quotient_fibre_cleared a b c x y u nonzero,fibre_source]
  change circleFoldLinear alpha ix iy (_ • _)=_
  rw [map_smul,circleFoldLinear_apply,circleFoldValue_radix4Evaluate alpha x y ix iy hx hy]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]
end Field

#print axioms product_value
#print axioms line_adjugate
#print axioms line_times_adjugate
#print axioms norm_signed_product
#print axioms fibre_source
#print axioms local_division
#print axioms quotient_fibre_cleared
#print axioms normalized_fold_cleared
end AspisV8.ChordRationalAlgebra
