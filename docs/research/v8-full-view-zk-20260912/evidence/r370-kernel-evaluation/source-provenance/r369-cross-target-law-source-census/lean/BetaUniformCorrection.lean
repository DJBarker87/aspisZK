/- Source-shaped coefficient identities for the R19 quadratic channel fold.
   Existence of corrections at a source prefix is not assumed proven here. -/
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace AspisR19.BetaUniformCorrection
variable {F : Type*} [CommRing F]

/- rR=P(rq,wr), rG=P(rq,wg), gR=P(qg,wr), gG=P(qg,wg)
   denotes any one of the seven coefficient positions. -/
theorem expansion (rR rG gR gG s beta : F) :
    (1-beta)*((1-beta)*rR+beta*rG)+s*beta*((1-beta)*gR+beta*gG) =
    (1-beta)^2*rR+beta*(1-beta)*(rG+s*gR)+s*beta^2*gG := by ring

theorem coefficient_zero (rR rG gR gG s beta : F)
    (hr : rR=0) (hc : rG+s*gR=0) (hg : gG=0) :
    (1-beta)*((1-beta)*rR+beta*rG)+s*beta*((1-beta)*gR+beta*gG)=0 := by
  rw [expansion,hr,hc,hg]
  ring

theorem all_seven (rR rG gR gG : Fin 7 → F) (s : F)
    (hr : ∀ i, rR i=0) (hc : ∀ i, rG i+s*gR i=0)
    (hg : ∀ i, gG i=0) : ∀ beta i,
    (1-beta)*((1-beta)*rR i+beta*rG i)+
      s*beta*((1-beta)*gR i+beta*gG i)=0 := by
  intro beta i
  exact coefficient_zero _ _ _ _ _ _ (hr i) (hc i) (hg i)

/- Apply to boundary moments: the same cross identity retains p2, so no
   new p2 assumption is hidden in removing its separate solve row. -/
theorem p2_retained (r0 r1 g0 g1 s : F)
    (hr : r0=0) (hc : r1+s*g0=0) (hg : g1=0) :
    s*(g1-g0)-(r1-r0)=0 := by
  rw [hr,hg]
  calc
    _ = -(r1+s*g0) := by ring
    _ = 0 := by rw [hc,neg_zero]

section CoefficientModel
variable {I J : Type*} [Fintype I] [Fintype J]

/- For the source, I and J are (chunk, slot). A coefficient kernel is zero
   between chunks and outside the convolution diagonal. Reversed weight
   slots and the quarter factor belong to C, not to a new assumption. -/
def coefficient (C : I → J → F) (q : I → F) (w : J → F) : F :=
  ∑ i, ∑ j, C i j * q i * w j

theorem coefficient_left (C : I → J → F) (q r : I → F) (w : J → F)
    (a b : F) : coefficient C (fun i => a*q i+b*r i) w =
    a*coefficient C q w+b*coefficient C r w := by
  have term : ∀ i j, C i j*(a*q i+b*r i)*w j =
      a*(C i j*q i*w j)+b*(C i j*r i*w j) := by intros; ring
  simp only [coefficient, term, Finset.sum_add_distrib, Finset.mul_sum]

theorem coefficient_right (C : I → J → F) (q : I → F) (w v : J → F)
    (a b : F) : coefficient C q (fun j => a*w j+b*v j) =
    a*coefficient C q w+b*coefficient C q v := by
  have term : ∀ i j, C i j*q i*(a*w j+b*v j) =
      a*(C i j*q i*w j)+b*(C i j*q i*v j) := by intros; ring
  simp only [coefficient, term, Finset.sum_add_distrib, Finset.mul_sum]

theorem folded_coefficient_zero (C : I → J → F) (r g : I → F)
    (wr wg : J → F) (s beta : F)
    (hr : coefficient C r wr=0)
    (hc : coefficient C r wg+s*coefficient C g wr=0)
    (hg : coefficient C g wg=0) :
    coefficient C (fun i => (1-beta)*r i+s*beta*g i)
      (fun j => (1-beta)*wr j+beta*wg j)=0 := by
  rw [coefficient_left, coefficient_right, coefficient_right]
  have h := coefficient_zero (coefficient C r wr) (coefficient C r wg)
    (coefficient C g wr) (coefficient C g wg) s beta hr hc hg
  simpa only [mul_assoc] using h
end CoefficientModel

/- q_i is paired with w_(4-j)%4 by the retained reversed dual convention.
   Fin 4 ensures this is [0,3,2,1]. This model still needs a Rust semantics
   correspondence; no extraction of the loop or field code is claimed. -/
def sourceKernel (n k : Nat) (quarter : F)
    (i j : Fin n × Fin 4) : F :=
  if i.1=j.1 ∧ i.2.val+(4-j.2.val)%4=k then quarter else 0

#print axioms expansion
#print axioms coefficient_zero
#print axioms all_seven
#print axioms p2_retained
#print axioms coefficient_left
#print axioms coefficient_right
#print axioms folded_coefficient_zero
end AspisR19.BetaUniformCorrection
