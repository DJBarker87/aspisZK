import AspisV8R19.TwoSwapResidualPolynomial
import AspisV8R19.ResidualDegree

/-! Degree for the new fixed-query polynomial, not the old 111-coordinate
minor. Query-section coefficients are constants; the G boundary is retained. -/
namespace AspisR19.TwoSwapResidualDegree
open MvPolynomial ResidualDegree HighRepairInvariant BetaUniformCorrection
noncomputable section
variable {F : Type*} [CommRing F]

theorem full_code_degree (z : Fin 10 → Poly (F:=F))
    (hz : ∀ i, (z i).totalDegree ≤ 1) (which : Nat) (j : Fin 131) :
    (TwoSwapSourceWeights.codeWeight
      (fun r => AspisV8R17.sourcePointBasis (ResidualModel.point z which) r.val) j).totalDegree ≤ 55 := by
  simp only [TwoSwapSourceWeights.codeWeight,FullPointFunctional.source_tensor]
  apply sub_bound (tensor_degree _ (point_degree z hz which) _)
  split_ifs
  · exact tensor_degree _ (point_degree z hz which) _
  · simp

theorem point_weight_degree (half : F) (a b c : Poly (F:=F)) (z : Fin 10 → Poly (F:=F))
    (ha : a.totalDegree ≤ 2) (hb : b.totalDegree ≤ 2) (hc : c.totalDegree ≤ 2)
    (hz : ∀ i, (z i).totalDegree ≤ 1) (which : Nat) (i : Index 32) :
    (TwoSwapResidualModel.pointWeight (C half) a b c z which i).totalDegree ≤ 57 := by
  apply totalDegree_finsetSum_le
  intro j _
  exact mul_bound (full_code_degree z hz which j)
    (chord_degree half a b c 2 _ j.val ha hb hc)

theorem g_degree (half : F) (a b c : Poly (F:=F))
    (ha : a.totalDegree ≤ 2) (hb : b.totalDegree ≤ 2) (hc : c.totalDegree ≤ 2) (i : Index 32) :
    (TwoSwapResidualModel.gBoundary (C half) a b c i).totalDegree ≤ 2 := by
  unfold TwoSwapResidualModel.gBoundary
  exact (mul_bound (by simpa only [totalDegree_C,mul_zero] using
      (totalDegree_pow (C half : Poly) 10) : ((C half : Poly)^10).totalDegree ≤ 0)
    (chord_degree half a b c 2 _ 128 ha hb hc)).trans (by decide)

theorem weight_degree (half : F) (a b c kappa : Poly (F:=F)) (z : Fin 10 → Poly (F:=F))
    (ha : a.totalDegree ≤ 2) (hb : b.totalDegree ≤ 2) (hc : c.totalDegree ≤ 2)
    (hk : kappa.totalDegree ≤ 1) (hz : ∀ i, (z i).totalDegree ≤ 1)
    (structured : Bool) (i : Index 32) :
    (TwoSwapResidualModel.weight (C half) a b c kappa z structured i).totalDegree ≤ 60 := by
  have he := point_weight_degree half a b c z ha hb hc hz
  have hkpow (n : Nat) : (kappa^n).totalDegree ≤ n :=
    (totalDegree_pow _ _).trans (by nlinarith)
  unfold TwoSwapResidualModel.weight
  apply add_bound
  · apply add_bound
    · apply (mul_bound hk ?_).trans (by decide : 1+57≤60)
      cases structured
      · exact he 0 i
      · exact (g_degree half a b c ha hb hc i).trans (by decide)
    · exact (mul_bound (hkpow 2) (he 1 i)).trans (by decide)
  · exact mul_bound (hkpow 3) (he 2 i)

theorem column_degree (v : Fin 13 → Fin 32 → F) (alpha : Poly (F:=F))
    (ha : alpha.totalDegree ≤ 1) (j : Fin 13) (i : Index 32) :
    (TwoSwapResidualModel.column (fun j i => C (v j i)) alpha j i).totalDegree ≤ 3 := by
  have hp : (alpha^(TwoSwapWitness.slot j).val).totalDegree ≤ 3 :=
    (totalDegree_pow _ _).trans (by have := (TwoSwapWitness.slot j).isLt; nlinarith)
  unfold TwoSwapResidualModel.column
  apply (mul_bound (by simp : (C (v j i.1) : Poly).totalDegree ≤ 0) ?_).trans (by decide : 0+3≤3)
  apply sub_bound
  · split_ifs <;> simp
  · apply mul_constant hp
    split_ifs <;> simp

theorem coefficient_degree (quarter : F) (q w : Index 32 → Poly (F:=F))
    (hq : ∀ i, (q i).totalDegree ≤ 3) (hw : ∀ i, (w i).totalDegree ≤ 60) (k : Nat) :
    (coefficient (sourceKernel 32 k (C quarter)) q w).totalDegree ≤ 63 := by
  apply totalDegree_finsetSum_le
  intro i _
  apply totalDegree_finsetSum_le
  intro j _
  have hk : (sourceKernel 32 k (C quarter : Poly) i j).totalDegree ≤ 0 := by
    unfold sourceKernel
    split_ifs <;> simp
  exact mul_bound (mul_bound hk (hq i)) (hw j)

theorem observation_degree (half quarter : F) (a b c kappa alpha : Poly (F:=F))
    (z : Fin 10 → Poly (F:=F)) (v : Fin 13 → Fin 32 → F)
    (ha : a.totalDegree ≤ 2) (hb : b.totalDegree ≤ 2) (hc : c.totalDegree ≤ 2)
    (hk : kappa.totalDegree ≤ 1) (halpha : alpha.totalDegree ≤ 1)
    (hz : ∀ i, (z i).totalDegree ≤ 1) (row : Nat) (j : Fin 13) :
    (TwoSwapResidualModel.observed (C half) (C quarter) a b c kappa z
      (TwoSwapResidualModel.column (fun j i => C (v j i)) alpha j) row).totalDegree ≤ 63 := by
  have hq := column_degree v alpha halpha j
  have hw := weight_degree half a b c kappa z ha hb hc hk hz
  unfold TwoSwapResidualModel.observed
  split_ifs
  · apply totalDegree_finsetSum_le
    intro i _
    exact (mul_bound (hq i) (point_weight_degree half a b c z ha hb hc hz row i)).trans (by decide)
  · exact coefficient_degree quarter _ _ hq (hw false) _
  · exact coefficient_degree quarter _ _ hq (hw true) _

theorem entry_degree [Nontrivial F] (half quarter : F) (v : Fin 13 → Fin 32 → F) (i j : Fin 13) :
    (TwoSwapResidualPolynomial.polynomial half quarter v i j).totalDegree ≤ 63 := by
  have hmul : ((X (12:Fin 36)*X 13 : Poly (F:=F))).totalDegree ≤ 2 := by
    simpa using totalDegree_mul (X (12:Fin 36) : Poly (F:=F)) (X 13)
  unfold TwoSwapResidualPolynomial.polynomial TwoSwapResidualPolynomial.normalizedMatrix TwoSwapResidualModel.matrix
  apply observation_degree
  · exact add_bound (by simp) hmul
  · exact sub_bound hmul (by simp)
  · rw [totalDegree_neg]
    exact add_bound (by simp) (by simp)
  · simp
  · simp
  · intro r; simp

theorem determinant_degree [Nontrivial F] (half quarter : F) (v : Fin 13 → Fin 32 → F) :
    (TwoSwapResidualPolynomial.polynomial half quarter v).det.totalDegree ≤ 819 := by
  simpa using AspisV8R17.minor_totalDegree (TwoSwapResidualPolynomial.polynomial half quarter v) 63
    (entry_degree half quarter v)

#print axioms full_code_degree
#print axioms point_weight_degree
#print axioms g_degree
#print axioms weight_degree
#print axioms column_degree
#print axioms coefficient_degree
#print axioms observation_degree
#print axioms entry_degree
#print axioms determinant_degree
end
end AspisR19.TwoSwapResidualDegree
