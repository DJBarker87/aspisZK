import AspisV8R19.R745JointObservationPolynomial
import AspisV8R17.MinorDegree

set_option autoImplicit false
namespace AspisV8R19.R842SparseCoefficientDegree
open MvPolynomial
open AspisV8R19.R745JointObservationPolynomial
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R738JointObservationModel
noncomputable section
variable {F : Type*} [Field F]

theorem rowWeight_degree (n k : Nat) (quarter : F)
    (w : Fin n × Fin 4 → JointPoly F) (D : Nat)
    (hw : ∀ i, (w i).totalDegree ≤ D) (d : Fin n) (slot : Fin 4) :
    (rowWeight n k (C quarter) w d slot).totalDegree ≤ D := by
  unfold rowWeight
  apply totalDegree_finsetSum_le
  intro t _
  have hc : (if slot.val+(4-t.val)%4=k then (C quarter : JointPoly F) else 0).totalDegree ≤ 0 := by
    split <;> simp
  exact (totalDegree_mul _ _).trans (by simpa using Nat.add_le_add hc (hw (d,t)))

theorem sparse_coefficient_degree (half quarter : F) (D : Nat)
    (hw : ∀ i, (rawOrdinaryWeight (C half) (1+pU*pV) (pU*pV-1)
      (-(pU+pV)) pKappa pTau (pZ (F:=F)) i).totalDegree ≤ D)
    (d : Fin 255) (s : Fin 3) (k : Fin 5) :
    (polynomialEntry half quarter d s (.inr (.inr k))).totalDegree ≤ D+3 := by
  change (sparseObservation (C half) (C quarter) (1+pU*pV) (pU*pV-1)
    (-(pU+pV)) pKappa pTau pAlpha (pZ (F:=F)) d s (.inr (.inr k))).totalDegree ≤ D+3
  unfold sparseObservation
  have ha : ((pAlpha (F:=F))^(s.val+1)).totalDegree ≤ 3 := by
    have hx : (pAlpha (F:=F)).totalDegree ≤ 1 := by simp [pAlpha]
    exact (totalDegree_pow _ _).trans ((Nat.mul_le_mul_left _ hx).trans (by omega))
  have hr (dd : Fin 256) (ss : Fin 4) :
      (rowWeight 256 (relationIndex k) (C quarter)
        (fun i => rawOrdinaryWeight (C half) (1+pU*pV) (pU*pV-1)
          (-(pU+pV)) pKappa pTau (pZ (F:=F)) (4*i.1.val+i.2.val)) dd ss).totalDegree ≤ D :=
    rowWeight_degree 256 (relationIndex k) quarter _ D (fun i => hw _) dd ss
  have hm (dd : Fin 256) :
      (pAlpha^(s.val+1) * rowWeight 256 (relationIndex k) (C quarter)
        (fun i => rawOrdinaryWeight (C half) (1+pU*pV) (pU*pV-1)
          (-(pU+pV)) pKappa pTau (pZ (F:=F)) (4*i.1.val+i.2.val)) dd 0).totalDegree ≤ D+3 :=
    (totalDegree_mul _ _).trans ((Nat.add_le_add ha (hr dd 0)).trans (by omega))
  exact (totalDegree_sub _ _).trans
    (max_le ((totalDegree_sub _ _).trans (max_le ((hr _ _).trans (by omega)) (hm _)))
      ((totalDegree_sub _ _).trans (max_le ((hr _ _).trans (by omega)) (hm _))))

#print axioms rowWeight_degree
#print axioms sparse_coefficient_degree
end
end AspisV8R19.R842SparseCoefficientDegree
