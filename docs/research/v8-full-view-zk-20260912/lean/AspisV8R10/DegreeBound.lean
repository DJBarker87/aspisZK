import Mathlib.Algebra.Polynomial.Degree.Lemmas

set_option autoImplicit false
namespace AspisV8R10
open Polynomial
variable {K : Type*} [CommRing K]

private theorem add_bound {p q : Polynomial K} {n : Nat}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (p + q).natDegree ≤ n :=
  (natDegree_add_le p q).trans (max_le hp hq)

private theorem mul_bound {p q : Polynomial K} {m n : Nat}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    (p * q).natDegree ≤ m + n :=
  natDegree_mul_le.trans (Nat.add_le_add hp hq)

private theorem const_mul_bound (a : K) {p : Polynomial K} {n : Nat}
    (hp : p.natDegree ≤ n) : (C a * p).natDegree ≤ n := by
  have hc : (C a).natDegree ≤ 0 := by simp
  simpa using mul_bound hc hp

theorem multiplier_degree_le_ten
    (d0 d1 d2 d3 eq active : Polynomial K) (theta28 mu mu2 eta : K)
    (h0 : d0.natDegree ≤ 2) (h1 : d1.natDegree ≤ 2)
    (h2 : d2.natDegree ≤ 2) (h3 : d3.natDegree ≤ 2)
    (he : eq.natDegree ≤ 1) (ha : active.natDegree ≤ 1) :
    (C eta * (C theta28 * ((eq * active) * ((d0 * d1) * (d2 * d3))) +
      C mu + C mu2 * (1 - active))).natDegree ≤ 10 := by
  have hd01 : (d0 * d1).natDegree ≤ 4 := mul_bound h0 h1
  have hd23 : (d2 * d3).natDegree ≤ 4 := mul_bound h2 h3
  have hd : ((d0 * d1) * (d2 * d3)).natDegree ≤ 8 := mul_bound hd01 hd23
  have hea : (eq * active).natDegree ≤ 2 := mul_bound he ha
  have hmain : (C theta28 * ((eq * active) * ((d0 * d1) * (d2 * d3)))).natDegree ≤ 10 :=
    const_mul_bound theta28 (mul_bound hea hd)
  have hmu : (C mu).natDegree ≤ 10 := by simp
  have hi : (1 - active).natDegree ≤ 1 := by
    exact (natDegree_sub_le 1 active).trans (max_le (by simp) ha)
  have hmu2 : (C mu2 * (1 - active)).natDegree ≤ 10 :=
    (const_mul_bound mu2 hi).trans (by decide)
  exact const_mul_bound eta (add_bound (add_bound hmain hmu) hmu2)

theorem row_influence_degree_le_eleven (k h : Polynomial K)
    (hk : k.natDegree ≤ 10) (hh : h.natDegree ≤ 1) :
    (k * h).natDegree ≤ 11 := mul_bound hk hh

theorem sum_influence_degree_le_eleven {ι : Type*} (s : Finset ι)
    (p : ι → Polynomial K) (hp : ∀ i ∈ s, (p i).natDegree ≤ 11) :
    (∑ i ∈ s, p i).natDegree ≤ 11 := by
  classical
  revert hp
  induction s using Finset.induction_on with
  | empty => intro hp; simp
  | @insert a s ha ih =>
      intro hp
      rw [Finset.sum_insert ha]
      apply add_bound
      · exact hp a (Finset.mem_insert_self a s)
      · exact ih (fun i hi => hp i (Finset.mem_insert_of_mem hi))

theorem high_coefficients_annihilate (p : Polynomial K)
    (hp : p.natDegree ≤ 11) (j : Nat) (hj : 12 ≤ j) : p.coeff j = 0 := by
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt hp (Nat.lt_of_succ_le hj))

#print axioms multiplier_degree_le_ten
#print axioms row_influence_degree_le_eleven
#print axioms sum_influence_degree_le_eleven
#print axioms high_coefficients_annihilate
end AspisV8R10
