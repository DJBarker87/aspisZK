import R1Z.PV_RunJoin_BoundaryWords73
import R1Z.PV_RunJoin_AccPolynomial38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BoundaryPolynomial73
open Aeneas Aeneas.Std ProverRwFull Polynomial
open PV_RunJoin_FieldData34 (value)
open PV_RunJoin_AccPolynomial38 (poly)
open scoped BigOperators
abbrev Q := aspis_core.field.QM31
abbrev K := AspisR1.ExtractedCurrentQM31Exact.QM31Exact
abbrev M := ZMod AspisCircleGroupOrder.P

def limb (q : Q) : Fin 4 → U32 := ![q.c0.a,q.c0.b,q.c1.a,q.c1.b]
def component (q : K) : Fin 4 → M := ![q.re.re,q.re.im,q.im.re,q.im.im]
def sum (p : Nat → Q) : Nat → Nat → K
  | 0,_ => 0
  | n+1,j => value (p j)+sum p n (j+1)

theorem component_decode (q : Q) (k : Fin 4) :
    component (value q) k=((limb q k).val : M) := by fin_cases k <;> rfl

theorem component_add (x y : K) (k : Fin 4) :
    component (x+y) k=component x k+component y k := by fin_cases k <;> rfl

theorem component_twice (x : K) (k : Fin 4) : component (2*x) k=2*component x k := by
  rw [two_mul,component_add,two_mul]

theorem component_sum (p : Nat → Q) (n j : Nat) (k : Fin 4) :
    component (sum p n j) k=(PV_RunJoin_BoundaryWords73.sum (fun i => limb (p i) k) n j : M) := by
  induction n generalizing j with
  | zero => fin_cases k <;> rfl
  | succ n ih => rw [sum,component_add,component_decode,ih,PV_RunJoin_BoundaryWords73.sum,Nat.cast_add]

theorem output_value (p : Nat → Q) (out : Q)
    (limbs : ∀ k : Fin 4,(limb out k).val=
      (2*(limb (p 0) k).val+PV_RunJoin_BoundaryWords73.sum (fun i => limb (p i) k) 27 1)%AspisCircleGroupOrder.P) :
    value out=2*value (p 0)+sum p 27 1 := by
  have h (k : Fin 4) : component (value out) k=component (2*value (p 0)+sum p 27 1) k := by
    rw [component_decode,limbs k]
    rw [ZMod.natCast_mod,component_add,component_twice,component_decode,component_sum,Nat.cast_add,Nat.cast_mul]
    rfl
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · exact h 0
    · exact h 1
  · apply QuadraticAlgebra.ext
    · exact h 2
    · exact h 3

theorem sum_poly (p : Nat → Q) (n j : Nat) :
    sum p n j=∑ k ∈ Finset.range n,value (p (j+k)) := by
  induction n generalizing j with
  | zero => simp only [sum,Finset.range_zero,Finset.sum_empty]
  | succ n ih =>
    rw [sum,ih,Finset.sum_range_succ']
    simp only [Nat.add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    congr 2
    omega

theorem polynomial_boundary (p : Nat → Q) :
    2*value (p 0)+sum p 27 1=(poly p).eval 0+(poly p).eval 1 := by
  have hz : (poly p).eval 0=value (p 0) := by
    rw [←Polynomial.coeff_zero_eq_eval_zero,poly,ProverCommitInterpolationRow48.qpoly,
      ProverCommitInterpolationPoly48.coeff,if_pos (by decide)]
    rfl
  have ho : (poly p).eval 1=value (p 0)+sum p 27 1 := by
    simp only [poly,ProverCommitInterpolationRow48.qpoly,ProverCommitInterpolationPoly48.poly,
      Polynomial.eval_finset_sum,Polynomial.eval_monomial,one_pow,mul_one]
    rw [Finset.sum_range_succ',sum_poly]
    simp only [Nat.add_comm 1]
    rw [add_comm]
    rfl
  rw [hz,ho]
  ring

#print axioms component_decode
#print axioms component_add
#print axioms component_twice
#print axioms component_sum
#print axioms output_value
#print axioms sum_poly
#print axioms polynomial_boundary
end R1Z.PV_RunJoin_BoundaryPolynomial73
