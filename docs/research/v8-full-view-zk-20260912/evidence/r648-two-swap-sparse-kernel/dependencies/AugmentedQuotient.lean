import AspisV8R19.AugmentedQuerySection
import AspisV8R19.NormalizedQuotient
import AspisV8R19.FullCoefficientBoundary

/-! The augmented section retains both complete seven-coefficient channel
maps, not just a post-beta mixture. Constant-low premises are explicit;
their two-swap source specialization is a separate certificate. -/
set_option autoImplicit false
namespace AspisR19.AugmentedQuotient
open HighRepairInvariant BetaUniformCorrection NormalizedQuotient
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def lift (alpha : F) (s : Fin 4) (v : Fin 32 → F) (i : Index 32) : F :=
  v i.1 * slotFactor alpha s i.2

theorem lift_sum (alpha : F) (s : Fin 4) (v : Fin 32 → F) (i : Index 32) :
    lift alpha s v i = ∑ d, v d * column alpha d s i := by
  simp [lift,column,unit,slotFactor,Prod.ext_iff,ite_and,mul_sub,
    Finset.sum_sub_distrib,mul_ite]

theorem lift_point (alpha : F) (s : Fin 4) (v : Fin 32 → F) (w : Index 32 → F) :
    (∑ i, lift alpha s v i * w i) =
      ∑ d, v d * (w (d,s)-alpha^s.val*w (d,0)) := by
  simp only [lift_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simp only [mul_assoc]
  rw [← Finset.mul_sum,column_point]

theorem lift_coefficient (quarter alpha : F) (s : Fin 4) (v : Fin 32 → F)
    (w : Index 32 → F) (k : Nat) :
    coefficient (sourceKernel 32 k quarter) (lift alpha s v) w =
      ∑ d, v d * localCoeff quarter alpha d s w k := by
  simp only [coefficient,lift_sum,Finset.mul_sum,Finset.sum_mul]
  calc
    _ = ∑ i, ∑ d, ∑ j, sourceKernel 32 k quarter i j * (v d * column alpha d s i) * w j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ d, ∑ i, ∑ j, sourceKernel 32 k quarter i j * (v d * column alpha d s i) * w j := by
      rw [Finset.sum_comm]
    _ = ∑ d, v d * coefficient (sourceKernel 32 k quarter) (column alpha d s) w := by
      apply Finset.sum_congr rfl
      intro d _
      simp only [coefficient,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp only [column_coefficient]

def quotient (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (alpha : F) (d : Fin 32) (s : Fin 4) : Index 32 → F :=
  lift alpha s (AugmentedQuerySection.normalized t ht noneOne d)

theorem quotient_fold (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (alpha : F) (d : Fin 32) (s : Fin 4) (i : Fin 32) :
    ∑ k : Fin 4, alpha^k.val * quotient t ht noneOne alpha d s (i,k) = 0 := by
  have h : ∀ k : Fin 4, alpha^k.val * quotient t ht noneOne alpha d s (i,k) =
      AugmentedQuerySection.normalized t ht noneOne d i * (alpha^k.val * slotFactor alpha s k) := by
    intro k; unfold quotient lift; ring
  simp only [h,← Finset.mul_sum,slot_fold,mul_zero]

theorem quotient_root (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (alpha : F) (d : Fin 32) (s k : Fin 4) (j : Fin 22) :
    NormalizedQuerySection.evaluate (fun i => quotient t ht noneOne alpha d s (i,k)) (t j) = 0 := by
  have h : ∀ i : Fin 32,
      quotient t ht noneOne alpha d s (i,k) * AspisCircleTensorBinding.naturalLineValue (t j) i.val =
      (AugmentedQuerySection.normalized t ht noneOne d i *
        AspisCircleTensorBinding.naturalLineValue (t j) i.val) * slotFactor alpha s k := by
    intro i; unfold quotient lift; ring
  simp only [NormalizedQuerySection.evaluate,h,← Finset.sum_mul]
  rw [show (∑ i, AugmentedQuerySection.normalized t ht noneOne d i *
    AspisCircleTensorBinding.naturalLineValue (t j) i.val)=0 from
      AugmentedQuerySection.normalized_query_root t ht noneOne d j,zero_mul]

theorem point_transport (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (alpha : F) (d : Fin 32) (s : Fin 4)
    (w : Index 32 → F)
    (hw : ∀ i : Fin 32, i.val<23 →
      w (i,s)-alpha^s.val*w (i,0)=w (0,s)-alpha^s.val*w (0,0)) :
    (∑ i, quotient t ht noneOne alpha d s i * w i) =
      (∑ i, column alpha d s i*w i)-(∑ i, column alpha 0 s i*w i) := by
  rw [column_point,column_point]
  exact (lift_point alpha s _ w).trans
    (AugmentedQuerySection.constant_low_transport t ht noneOne d _ hw)

theorem coefficient_transport (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (quarter alpha : F) (d : Fin 32) (s : Fin 4)
    (w : Index 32 → F) (k : Nat)
    (hw : ∀ i : Fin 32, i.val<23 →
      localCoeff quarter alpha i s w k=localCoeff quarter alpha 0 s w k) :
    coefficient (sourceKernel 32 k quarter) (quotient t ht noneOne alpha d s) w =
      localCoeff quarter alpha d s w k-localCoeff quarter alpha 0 s w k := by
  exact (lift_coefficient quarter alpha s _ w k).trans
    (AugmentedQuerySection.constant_low_transport t ht noneOne d _ hw)

#print axioms lift_sum
#print axioms lift_point
#print axioms lift_coefficient
#print axioms quotient_fold
#print axioms quotient_root
#print axioms point_transport
#print axioms coefficient_transport
end
end AspisR19.AugmentedQuotient
