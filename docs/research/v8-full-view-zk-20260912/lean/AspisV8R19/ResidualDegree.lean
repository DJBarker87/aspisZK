/- Degree accounting for the explicit root/point/chord-substituted model. -/
import AspisV8R19.SourceResidualPolynomial
import AspisV8R17.MinorDegree
import Mathlib.Tactic.FinCases

namespace AspisR19.ResidualDegree
open MvPolynomial ResidualModel SourceResidualPolynomial
variable {F : Type*} [CommRing F]
abbrev Poly := MvPolynomial (Fin 36) F
noncomputable section

theorem add_bound {p q : Poly (F:=F)} {d : Nat}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) : (p+q).totalDegree ≤ d :=
  (totalDegree_add _ _).trans (max_le hp hq)
theorem sub_bound {p q : Poly (F:=F)} {d : Nat}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) : (p-q).totalDegree ≤ d :=
  (totalDegree_sub _ _).trans (max_le hp hq)
theorem mul_bound {p q : Poly (F:=F)} {a b : Nat}
    (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) : (p*q).totalDegree ≤ a+b :=
  (totalDegree_mul _ _).trans (Nat.add_le_add hp hq)
theorem mul_constant {p q : Poly (F:=F)} {d : Nat}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ 0) : (p*q).totalDegree ≤ d := by
  simpa using mul_bound hp hq

theorem x_degree (half : F) (j r : Nat) :
    (xEntry (C half : Poly) j r).totalDegree ≤ 0 := by
  rw [← map_xEntry C half j r]
  simp
theorem xx_degree (half : F) (j r : Nat) :
    (xxEntry (C half : Poly) j r).totalDegree ≤ 0 := by
  rw [← map_xxEntry C half j r]
  simp
theorem delta_degree (j r : Nat) : (delta j r : Poly (F:=F)).totalDegree ≤ 0 := by
  unfold delta
  split_ifs <;> simp

theorem chord_degree (half : F) (a b c : Poly (F:=F)) (d j r : Nat)
    (ha : a.totalDegree ≤ d) (hb : b.totalDegree ≤ d) (hc : c.totalDegree ≤ d) :
    (chordEntry (C half) a b c j r).totalDegree ≤ d := by
  unfold chordEntry
  split_ifs
  · exact add_bound (mul_constant ha (delta_degree _ _)) (mul_constant hb (x_degree _ _ _))
  · exact mul_constant hc (delta_degree _ _)
  · exact mul_constant hc (sub_bound (delta_degree _ _) (xx_degree _ _ _))
  · exact add_bound (mul_constant ha (delta_degree _ _)) (mul_constant hb (x_degree _ _ _))

theorem carry_degree (z : Fin 10 → Poly (F:=F))
    (hz : ∀ i, (z i).totalDegree ≤ 1) (i : Fin 10) :
    (carry z i).totalDegree ≤ 9-i.val := by
  unfold carry
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ k : Fin 10, (if i.val<k.val then 1 else 0 : Nat) := by
      apply Finset.sum_le_sum
      intro k _
      split_ifs <;> simp_all
    _ = 9-i.val := by fin_cases i <;> decide

theorem point_degree (z : Fin 10 → Poly (F:=F))
    (hz : ∀ i, (z i).totalDegree ≤ 1) (which : Nat) (i : Fin 10) :
    (point z which i).totalDegree ≤ 10-i.val := by
  have hi : 1 ≤ 10-i.val := by omega
  have hc := carry_degree z hz i
  have htwo : ((2:Poly (F:=F))*z i*carry z i).totalDegree ≤ 10-i.val := by
    have hm := mul_bound (show (2:Poly (F:=F)).totalDegree ≤ 0 by
      change (C (2:F)).totalDegree ≤ 0
      simp) (hz i)
    exact (mul_bound hm hc).trans (by omega)
  unfold point
  split_ifs
  · exact (hz i).trans hi
  · exact sub_bound (add_bound ((hz i).trans hi) (hc.trans (by omega))) htwo
  · exact sub_bound (by simp) ((hz i).trans hi)
  · exact (hz i).trans hi

theorem tensor_degree (z : Fin 10 → Poly (F:=F))
    (hz : ∀ i, (z i).totalDegree ≤ 10-i.val) (r : Nat) :
    (tensor z r).totalDegree ≤ 55 := by
  unfold tensor
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ i : Fin 10, (10-i.val) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact sub_bound (by simp) (hz i)
      · exact hz i
    _ = 55 := by decide

theorem code_degree (order : Fin 111 → Nat) (inactive : Fin 111 → Bool)
    (z : Fin 10 → Poly (F:=F)) (hz : ∀ i, (z i).totalDegree ≤ 10-i.val) (j : Fin 111) :
    (codeWeight order inactive z j).totalDegree ≤ 55 := by
  unfold codeWeight
  apply sub_bound (tensor_degree z hz _)
  split_ifs
  · exact tensor_degree z hz _
  · simp

theorem point_weight_degree (order : Fin 111 → Nat) (inactive : Fin 111 → Bool)
    (half : F) (a b c : Poly (F:=F)) (z : Fin 10 → Poly (F:=F))
    (ha : a.totalDegree ≤ 2) (hb : b.totalDegree ≤ 2) (hc : c.totalDegree ≤ 2)
    (hz : ∀ i, (z i).totalDegree ≤ 1) (which r : Nat) :
    (pointWeight order inactive (C half) a b c z which r).totalDegree ≤ 57 := by
  apply totalDegree_finsetSum_le
  intro j _
  exact mul_bound (code_degree order inactive _ (point_degree z hz which) j)
    (chord_degree half a b c 2 r j.val ha hb hc)

theorem shift_degree (half : F) (n : Nat) (p : Fin 27 → Poly (F:=F)) (d : Nat)
    (hp : ∀ j, (p j).totalDegree ≤ d) (r : Fin 27) :
    (shift (C half) n p r).totalDegree ≤ d := by
  induction n generalizing r with
  | zero => exact hp r
  | succ n ih =>
    apply totalDegree_finsetSum_le
    intro j _
    exact mul_constant (ih j) (x_degree half j.val r.val)

theorem root_run_degree (half : F) (roots : List (Poly (F:=F)))
    (hr : ∀ x ∈ roots, x.totalDegree ≤ 1) (p : Fin 27 → Poly (F:=F)) (d : Nat)
    (hp : ∀ j, (p j).totalDegree ≤ d) (j : Fin 27) :
    (rootRun (C half) roots p j).totalDegree ≤ d+roots.length := by
  induction roots generalizing p d with
  | nil => simpa [rootRun] using hp j
  | cons x xs ih =>
    have hx := hr x (by simp)
    have hs : ∀ y ∈ xs, y.totalDegree ≤ 1 := by intro y hy; exact hr y (by simp [hy])
    have hn (r : Fin 27) :
        (shift (C half) 1 p r-x*p r).totalDegree ≤ d+1 := by
      apply sub_bound
      · exact (shift_degree half 1 p d hp r).trans (by omega)
      · exact (mul_bound hx (hp r)).trans (by omega)
    simpa [rootRun,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih hs _ (d+1) hn

theorem root_coefficients_degree (half : F) (roots : Fin 22 → Poly (F:=F))
    (hr : ∀ i, (roots i).totalDegree ≤ 1) (j : Fin 23) :
    (rootCoefficients (C half) roots j).totalDegree ≤ 22 := by
  unfold rootCoefficients
  have hl : ∀ x ∈ List.ofFn roots, x.totalDegree ≤ 1 := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact hr i
  have hp : ∀ j : Fin 27,
      (if j.val=0 then (1:Poly (F:=F)) else 0).totalDegree ≤ 0 := by
    intro j
    split_ifs <;> simp
  simpa using root_run_degree half (List.ofFn roots) hl _ 0 hp ⟨j.val,by omega⟩

theorem quotient_degree (half : F) (alpha : Poly (F:=F)) (p : Fin 23 → Poly (F:=F))
    (ha : alpha.totalDegree ≤ 1) (hp : ∀ j, (p j).totalDegree ≤ 22)
    (col : Fin 13) (r : Fin 108) :
    (quotient (C half) alpha p col r).totalDegree ≤ 25 := by
  have hpad : ∀ j : Fin 27,
      (if h : j.val<23 then p ⟨j.val,h⟩ else 0).totalDegree ≤ 22 := by
    intro j
    split_ifs
    · exact hp _
    · simp
  have hv := shift_degree half (col.val/3) _ 22 hpad ⟨r.val/4,by omega⟩
  have ha3 : (alpha^(col.val%3+1)).totalDegree ≤ 3 :=
    (totalDegree_pow _ _).trans (by have hm := col.val.mod_lt (by decide : 0<3); nlinarith)
  unfold quotient
  split_ifs
  · exact mul_bound (by simpa only [totalDegree_neg] using ha3) hv
  · exact hv.trans (by decide)
  · simp

theorem poly_degree (quarter : F) (q w : Fin 108 → Poly (F:=F)) (dq dw : Nat)
    (hq : ∀ j, (q j).totalDegree ≤ dq) (hw : ∀ j, (w j).totalDegree ≤ dw) (k : Nat) :
    (polyCoeff (C quarter) q w k).totalDegree ≤ dq+dw := by
  apply totalDegree_finsetSum_le
  intro block _
  apply totalDegree_finsetSum_le
  intro a _
  apply totalDegree_finsetSum_le
  intro b _
  split_ifs
  · exact (mul_bound (mul_bound (by simp : (C quarter : Poly).totalDegree ≤ 0) (hq _)) (hw _)).trans (by omega)
  · simp

#print axioms add_bound
#print axioms sub_bound
#print axioms mul_bound
#print axioms mul_constant
#print axioms x_degree
#print axioms xx_degree
#print axioms delta_degree
#print axioms chord_degree
#print axioms carry_degree
#print axioms point_degree
#print axioms tensor_degree
#print axioms code_degree
#print axioms point_weight_degree
#print axioms shift_degree
#print axioms root_run_degree
#print axioms root_coefficients_degree
#print axioms quotient_degree
#print axioms poly_degree
end
end AspisR19.ResidualDegree
