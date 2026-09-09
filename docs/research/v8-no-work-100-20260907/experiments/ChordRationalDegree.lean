import ChordRationalAlgebra
import Mathlib.Tactic.ComputeDegree

/-! Degree accounting for the denominator-cleared low-bit chord quotient.
The raw polynomial components remain abstract and need only their actual
degree cap.  This is not an arbitrary-oracle statement. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 100000
namespace AspisV8.ChordRationalDegree
open Polynomial
open AspisV8.ChordRationalAlgebra
open AspisV5FriConcreteEncoderCommutation
open AspisV5ComponentCConcreteFoldLinearity
noncomputable section

variable {K : Type*} [Field K]

def radialS : K[X] := X
def radialT : K[X] := 1-X

def finalFromRadial (s : K) : K := 2*s-1
def radialFromFinal (z : K) : K := (z+1)/2
def radialSubstitution : K[X] := C ((2:K)⁻¹)*(X+1)

theorem final_from_radial_injective (twoNonzero : (2:K)≠0) :
    Function.Injective (fun s : K=>finalFromRadial s) := by
  intro s t h
  simp only [finalFromRadial] at h
  have doubled : 2*s=2*t := by linear_combination h
  exact (mul_left_cancel₀ twoNonzero) doubled

theorem radial_from_final_inverse (twoNonzero : (2:K)≠0) (s : K) :
    radialFromFinal (finalFromRadial s)=s := by
  simp only [radialFromFinal,finalFromRadial]
  field_simp
  ring

theorem radial_substitution_eval (z : K) :
    radialSubstitution.eval z=radialFromFinal z := by
  simp [radialSubstitution,radialFromFinal,div_eq_mul_inv]
  ring

theorem radial_substitution_degree : (radialSubstitution (K:=K)).natDegree≤1 := by
  unfold radialSubstitution
  have hplus : (X+(1:K[X])).natDegree≤1 :=
    (natDegree_add_le X 1).trans (max_le natDegree_X_le (by simp))
  calc
    (C (2:K)⁻¹*(X+1)).natDegree≤(C (2:K)⁻¹).natDegree+(X+1).natDegree :=
      natDegree_mul_le
    _ ≤ 0+1 := Nat.add_le_add (by simp) hplus
    _ = 1 := rfl

theorem radial_comp_degree (p : K[X]) (d : Nat) (hp : p.natDegree≤d) :
    (p.comp radialSubstitution).natDegree≤d := by
  calc
    (p.comp radialSubstitution).natDegree≤p.natDegree*radialSubstitution.natDegree :=
      natDegree_comp_le
    _ ≤ d*1 := Nat.mul_le_mul hp radial_substitution_degree
    _ = d := Nat.mul_one d

def clearedAdjugate (a b c : K) : Fin 4 → K[X] :=
  adjugate (C a) (C b) (C c) radialS radialT

def clearedNorm (a b c : K) : K[X] :=
  norm (C a) (C b) (C c) radialS radialT

theorem cleared_adjugate_degree (a b c : K) :
    (clearedAdjugate a b c 0).natDegree≤1 ∧
    (clearedAdjugate a b c 1).natDegree≤1 ∧
    (clearedAdjugate a b c 2).natDegree≤1 ∧
    (clearedAdjugate a b c 3).natDegree≤0 := by
  refine ⟨?_,?_,?_,?_⟩
  · simp [clearedAdjugate,adjugate,radialS,radialT]
    compute_degree
  · simp [clearedAdjugate,adjugate,radialS,radialT]
    compute_degree
  · simp [clearedAdjugate,adjugate,radialS,radialT]
    compute_degree
  · change (2*C a*C b*C c : K[X]).natDegree≤0
    calc
      (2*C a*C b*C c : K[X]).natDegree
          ≤ (2*C a*C b : K[X]).natDegree+(C c).natDegree := natDegree_mul_le
      _ ≤ ((2:K[X])*C a).natDegree+(C b).natDegree+(C c).natDegree := by
        gcongr
        exact natDegree_mul_le
      _ ≤ (2:K[X]).natDegree+(C a).natDegree+(C b).natDegree+(C c).natDegree := by
        gcongr
        exact natDegree_mul_le
      _ ≤ 0 := by simp

theorem cleared_norm_degree (a b c : K) :
    (clearedNorm a b c).natDegree≤2 := by
  simp only [clearedNorm,ChordRationalAlgebra.norm]
  simp [radialS,radialT]
  compute_degree

private theorem add_bound {p q : K[X]} {d : Nat}
    (hp : p.natDegree≤d) (hq : q.natDegree≤d) :
    (p+q).natDegree≤d :=
  (natDegree_add_le p q).trans (max_le hp hq)

private theorem mul_bound {p q : K[X]} {dp dq : Nat}
    (hp : p.natDegree≤dp) (hq : q.natDegree≤dq) :
    (p*q).natDegree≤dp+dq :=
  natDegree_mul_le.trans (Nat.add_le_add hp hq)

private theorem radialT_degree : (radialT (K:=K)).natDegree≤1 := by
  unfold radialT
  exact (natDegree_sub_le 1 X).trans (max_le (by simp) natDegree_X_le)

private theorem scale_bound {p : K[X]} {d : Nat} (hp : p.natDegree≤d) :
    (radialS*p).natDegree≤d+1 ∧ (radialT*p).natDegree≤d+1 := by
  have hs : (radialS (K:=K)).natDegree≤1 := by simp [radialS]
  have ht : (radialT (K:=K)).natDegree≤1 := radialT_degree
  constructor
  · exact (mul_bound hs hp).trans (by omega)
  · exact (mul_bound ht hp).trans (by omega)

/-- Multiplying a four-component degree-d raw polynomial by the explicit
adjugate costs at most two radial degrees in the first three components and
one in the fourth.  The asymmetric last bound is what avoids a spurious 258. -/
theorem cleared_product_degree (a b c : K) (u : Fin 4 → K[X]) (d : Nat)
    (hu : ∀ j, (u j).natDegree≤d) :
    (product radialS radialT u (clearedAdjugate a b c) 0).natDegree≤d+2 ∧
    (product radialS radialT u (clearedAdjugate a b c) 1).natDegree≤d+2 ∧
    (product radialS radialT u (clearedAdjugate a b c) 2).natDegree≤d+2 ∧
    (product radialS radialT u (clearedAdjugate a b c) 3).natDegree≤d+1 := by
  have ha := cleared_adjugate_degree a b c
  rcases ha with ⟨ha0,ha1,ha2,ha3⟩
  have hs : (radialS (K:=K)).natDegree≤1 := by simp [radialS]
  have ht : (radialT (K:=K)).natDegree≤1 := radialT_degree
  have h00 : (u 0*clearedAdjugate a b c 0).natDegree≤d+2 :=
    (mul_bound (hu 0) ha0).trans (by omega)
  have ht11 : (radialT*u 1*clearedAdjugate a b c 1).natDegree≤d+2 :=
    (mul_bound (mul_bound ht (hu 1)) ha1).trans (by omega)
  have hs22 : (radialS*u 2*clearedAdjugate a b c 2).natDegree≤d+2 :=
    (mul_bound (mul_bound hs (hu 2)) ha2).trans (by omega)
  have hst33 :
      (radialS*radialT*u 3*clearedAdjugate a b c 3).natDegree≤d+2 :=
    (mul_bound (mul_bound (mul_bound hs ht) (hu 3)) ha3).trans (by omega)
  have h01 : (u 0*clearedAdjugate a b c 1).natDegree≤d+2 :=
    (mul_bound (hu 0) ha1).trans (by omega)
  have h10 : (u 1*clearedAdjugate a b c 0).natDegree≤d+2 :=
    (mul_bound (hu 1) ha0).trans (by omega)
  have h23 : (u 2*clearedAdjugate a b c 3).natDegree≤d+1 :=
    (mul_bound (hu 2) ha3).trans (by omega)
  have h32 : (u 3*clearedAdjugate a b c 2).natDegree≤d+1 :=
    (mul_bound (hu 3) ha2).trans (by omega)
  have hs23 :
      (radialS*(u 2*clearedAdjugate a b c 3+
        u 3*clearedAdjugate a b c 2)).natDegree≤d+2 :=
    (mul_bound hs (add_bound h23 h32)).trans (by omega)
  have h02 : (u 0*clearedAdjugate a b c 2).natDegree≤d+2 :=
    (mul_bound (hu 0) ha2).trans (by omega)
  have h20 : (u 2*clearedAdjugate a b c 0).natDegree≤d+2 :=
    (mul_bound (hu 2) ha0).trans (by omega)
  have h13 : (u 1*clearedAdjugate a b c 3).natDegree≤d+1 :=
    (mul_bound (hu 1) ha3).trans (by omega)
  have h31 : (u 3*clearedAdjugate a b c 1).natDegree≤d+1 :=
    (mul_bound (hu 3) ha1).trans (by omega)
  have ht13 :
      (radialT*(u 1*clearedAdjugate a b c 3+
        u 3*clearedAdjugate a b c 1)).natDegree≤d+2 :=
    (mul_bound ht (add_bound h13 h31)).trans (by omega)
  have h03 : (u 0*clearedAdjugate a b c 3).natDegree≤d+1 :=
    (mul_bound (hu 0) ha3).trans (by omega)
  have h30 : (u 3*clearedAdjugate a b c 0).natDegree≤d+1 :=
    (mul_bound (hu 3) ha0).trans (by omega)
  have h12 : (u 1*clearedAdjugate a b c 2).natDegree≤d+1 :=
    (mul_bound (hu 1) ha2).trans (by omega)
  have h21 : (u 2*clearedAdjugate a b c 1).natDegree≤d+1 :=
    (mul_bound (hu 2) ha1).trans (by omega)
  simp only [product,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three]
  constructor
  · exact add_bound (add_bound (add_bound h00 ht11) hs22) hst33
  constructor
  · exact add_bound (add_bound h01 h10) hs23
  constructor
  · exact add_bound (add_bound h02 h20) ht13
  · exact add_bound (add_bound (add_bound h03 h30) h12) h21

def foldedNumerator (alpha : K) (w : Fin 4 → K[X]) : K[X] :=
  w 0+C alpha*w 1+C alpha^2*w 2+C alpha^3*w 3

/-- The polynomial numerator evaluates to the actual natural-coefficient
arity-four fold at every radial coordinate. -/
theorem folded_numerator_eval (alpha z : K) (w : Fin 4 → K[X]) :
    (foldedNumerator alpha w).eval z=
      coefficientFoldValue alpha (fun j=>(w j).eval z) := by
  simp [foldedNumerator,coefficientFoldValue]

/-- Any arity-four fold of the cleared numerator has the same degree cap as
its first three components; challenges are field scalars. -/
theorem folded_numerator_degree (a b c alpha : K) (u : Fin 4 → K[X]) (d : Nat)
    (hu : ∀ j, (u j).natDegree≤d) :
    (foldedNumerator alpha
      (product radialS radialT u (clearedAdjugate a b c))).natDegree≤d+2 := by
  have h := cleared_product_degree a b c u d hu
  rcases h with ⟨h0,h1,h2,h3⟩
  let w := product radialS radialT u (clearedAdjugate a b c)
  change (foldedNumerator alpha w).natDegree≤d+2
  unfold foldedNumerator
  have h1' : (w 0).natDegree≤d+2 := by simpa [w] using h0
  have h2' : (C alpha*w 1).natDegree≤d+2 :=
    (mul_bound (dp:=0) (dq:=d+2) (by simp) h1).trans (by omega)
  have h3' : (C alpha^2*w 2).natDegree≤d+2 :=
    (mul_bound (dp:=0) (dq:=d+2) (by simp) h2).trans (by omega)
  have h4' : (C alpha^3*w 3).natDegree≤d+2 :=
    (mul_bound (dp:=0) (dq:=d+1) (by simp) h3).trans (by omega)
  exact add_bound (add_bound (add_bound h1' h2') h3') h4'

def clearedDiscrepancy (a b c alpha : K) (u : Fin 4 → K[X])
    (final : K[X]) : K[X] :=
  foldedNumerator alpha
      (product radialS radialT u (clearedAdjugate a b c))-
    clearedNorm a b c*final

theorem cleared_discrepancy_degree (a b c alpha : K) (u : Fin 4 → K[X])
    (final : K[X]) (d : Nat) (hu : ∀ j, (u j).natDegree≤d)
    (hfinal : final.natDegree≤d) :
    (clearedDiscrepancy a b c alpha u final).natDegree≤d+2 := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact folded_numerator_degree a b c alpha u d hu
  · exact (mul_bound (cleared_norm_degree a b c) hfinal).trans (by omega)

def rationalFold (a b c alpha : K) (u : Fin 4 → K[X]) (z : K) : K :=
  (foldedNumerator alpha
      (product radialS radialT u (clearedAdjugate a b c))).eval z /
    (clearedNorm a b c).eval z

theorem rational_match_is_discrepancy_root (a b c alpha z : K)
    (u : Fin 4 → K[X]) (final : K[X])
    (nonpole : (clearedNorm a b c).eval z≠0)
    (hmatch : rationalFold a b c alpha u z=final.eval z) :
    (clearedDiscrepancy a b c alpha u final).eval z=0 := by
  have cleared := (div_eq_iff nonpole).mp hmatch
  simp only [clearedDiscrepancy,eval_sub,eval_mul]
  exact sub_eq_zero.mpr (by simpa [mul_comm] using cleared)

section Counting
variable [DecidableEq K]

/-- A false degree-d final polynomial can match the constructed rational fold
on at most d+2 nonpole radial positions.  Pole positions are deliberately not
included; the source/domain bridge must account for them separately. -/
theorem nonpole_match_card_le (domain : Finset K) (a b c alpha : K)
    (u : Fin 4 → K[X]) (final : K[X]) (d : Nat)
    (hu : ∀ j, (u j).natDegree≤d) (hfinal : final.natDegree≤d)
    (different : clearedDiscrepancy a b c alpha u final≠0) :
    (domain.filter fun z => (clearedNorm a b c).eval z≠0 ∧
      rationalFold a b c alpha u z=final.eval z).card≤d+2 := by
  apply (Polynomial.card_le_degree_of_subset_roots (p:=
    clearedDiscrepancy a b c alpha u final) ?_).trans
    (cleared_discrepancy_degree a b c alpha u final d hu hfinal)
  intro z hz
  have pair := (Finset.mem_filter.mp hz).2
  exact (Polynomial.mem_roots different).mpr
    (rational_match_is_discrepancy_root a b c alpha z u final pair.1 pair.2)

theorem degree255_nonpole_match_card_le (domain : Finset K) (a b c alpha : K)
    (u : Fin 4 → K[X]) (final : K[X])
    (hu : ∀ j, (u j).natDegree≤255) (hfinal : final.natDegree≤255)
    (different : clearedDiscrepancy a b c alpha u final≠0) :
    (domain.filter fun z => (clearedNorm a b c).eval z≠0 ∧
      rationalFold a b c alpha u z=final.eval z).card≤257 := by
  simpa using nonpole_match_card_le domain a b c alpha u final 255 hu hfinal different

def possibleMatches (domain : Finset K) (a b c alpha : K)
    (u : Fin 4 → K[X]) (final : K[X]) : Finset K :=
  domain.filter fun z => (clearedNorm a b c).eval z=0 ∨
    rationalFold a b c alpha u z=final.eval z

/-- The at-most-two denominator poles are charged explicitly.  This avoids
conditioning on a nonpole schedule while proving the 259-position ceiling. -/
theorem degree255_possible_match_card_le (domain : Finset K) (a b c alpha : K)
    (u : Fin 4 → K[X]) (final : K[X])
    (hu : ∀ j, (u j).natDegree≤255) (hfinal : final.natDegree≤255)
    (normNonzero : clearedNorm a b c≠0)
    (different : clearedDiscrepancy a b c alpha u final≠0) :
    (possibleMatches domain a b c alpha u final).card≤259 := by
  let poles := domain.filter fun z=>(clearedNorm a b c).eval z=0
  let goodMatches := domain.filter fun z=>(clearedNorm a b c).eval z≠0 ∧
    rationalFold a b c alpha u z=final.eval z
  have split : possibleMatches domain a b c alpha u final=poles∪goodMatches := by
    ext z
    by_cases hz : (clearedNorm a b c).eval z=0 <;>
      simp [possibleMatches,poles,goodMatches,hz]
  have hpoles : poles.card≤2 := by
    apply (Polynomial.card_le_degree_of_subset_roots (p:=clearedNorm a b c) ?_).trans
      (cleared_norm_degree a b c)
    intro z hz
    exact (Polynomial.mem_roots normNonzero).mpr (Finset.mem_filter.mp hz).2
  have hmatches : goodMatches.card≤257 := by
    exact degree255_nonpole_match_card_le domain a b c alpha u final hu hfinal different
  rw [split]
  exact (Finset.card_union_le poles goodMatches).trans (by omega)

end Counting

#print axioms cleared_adjugate_degree
#print axioms final_from_radial_injective
#print axioms radial_from_final_inverse
#print axioms radial_substitution_eval
#print axioms radial_comp_degree
#print axioms cleared_norm_degree
#print axioms cleared_product_degree
#print axioms folded_numerator_eval
#print axioms folded_numerator_degree
#print axioms cleared_discrepancy_degree
#print axioms rational_match_is_discrepancy_root
#print axioms nonpole_match_card_le
#print axioms degree255_nonpole_match_card_le
#print axioms degree255_possible_match_card_le
end
end AspisV8.ChordRationalDegree
