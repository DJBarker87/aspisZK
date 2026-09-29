/- Total degree after the actual algebraic substitutions, not an IID theorem. -/
import AspisV8R19.ResidualDegree

namespace AspisR19.SourceResidualDegree
open MvPolynomial ResidualModel SourceResidualPolynomial ResidualDegree
variable {F : Type*} [CommRing F]
noncomputable section

theorem observation_degree (order : Fin 111 → Nat) (inactive : Fin 111 → Bool)
    (half quarter : F) (a b c κ alpha : Poly (F:=F))
    (z : Fin 10 → Poly (F:=F)) (p : Fin 23 → Poly (F:=F))
    (ha : a.totalDegree ≤ 2) (hb : b.totalDegree ≤ 2) (hc : c.totalDegree ≤ 2)
    (hk : κ.totalDegree ≤ 1) (halpha : alpha.totalDegree ≤ 1)
    (hz : ∀ i, (z i).totalDegree ≤ 1) (hp : ∀ j, (p j).totalDegree ≤ 22)
    (row : Nat) (col : Fin 13) :
    (observation order inactive (C half) (C quarter) a b c κ alpha z p row col).totalDegree ≤ 85 := by
  let e := fun which (r : Fin 108) => pointWeight order inactive (C half) a b c z which r.val
  have he (which : Nat) (r : Fin 108) : (e which r).totalDegree ≤ 57 :=
    point_weight_degree order inactive half a b c z ha hb hc hz which r.val
  have hq (r : Fin 108) := quotient_degree half alpha p halpha hp col r
  have hkpow (n : Nat) : (κ^n).totalDegree ≤ n :=
    (totalDegree_pow _ _).trans (by nlinarith)
  have hw (r : Fin 108) :
      (κ*e 0 r+κ^2*e 1 r+κ^3*e 2 r).totalDegree ≤ 60 := by
    apply add_bound
    · exact add_bound ((mul_bound hk (he 0 r)).trans (by decide))
        ((mul_bound (hkpow 2) (he 1 r)).trans (by decide))
    · exact mul_bound (hkpow 3) (he 2 r)
  have hg (r : Fin 108) : (κ^2*e 1 r+κ^3*e 2 r).totalDegree ≤ 60 :=
    add_bound ((mul_bound (hkpow 2) (he 1 r)).trans (by decide))
      (mul_bound (hkpow 3) (he 2 r))
  unfold observation
  split_ifs
  · simp
  · apply totalDegree_finsetSum_le
    intro r _
    exact (mul_bound (hq r) (he row r)).trans (by decide)
  · exact poly_degree quarter _ _ 25 60 hq hw _
  · exact poly_degree quarter _ _ 25 60 hq hg _

theorem entry_degree [Nontrivial F] (half quarter : F) (i j : Fin 13) :
    (polyMinor half quarter i j).totalDegree ≤ 85 := by
  have hmul : ((X (12:Fin 36)*X 13 : Poly (F:=F))).totalDegree ≤ 2 := by
    simpa using totalDegree_mul (X (12:Fin 36) : Poly (F:=F)) (X 13)
  unfold polyMinor normalizedMinor minor
  apply observation_degree
  · exact add_bound (by simp) hmul
  · exact sub_bound hmul (by simp)
  · rw [totalDegree_neg]
    exact add_bound (by simp) (by simp)
  · simp
  · simp
  · intro r; simp
  · apply root_coefficients_degree
    intro r; simp

theorem determinant_degree [Nontrivial F] (half quarter : F) :
    (polyMinor half quarter).det.totalDegree ≤ 1105 := by
  simpa using AspisV8R17.minor_totalDegree (polyMinor half quarter) 85 (entry_degree half quarter)

#print axioms observation_degree
#print axioms entry_degree
#print axioms determinant_degree
end
end AspisR19.SourceResidualDegree
