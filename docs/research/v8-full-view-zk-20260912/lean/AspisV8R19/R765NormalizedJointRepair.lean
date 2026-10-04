import AspisV8R19.R764RawJointWeights

namespace AspisV8R19.R765NormalizedJointRepair
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R739AugmentedQuery256
open AspisV8R19.R758NormalizedLowRepair
open AspisV8R19.R764RawJointWeights
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def pairedWeight (half quarter a b c kappa tau alpha : F) (z : Fin 10 → F)
    (row : ObservationRow) (d : Fin 256) (s : Fin 3) : F :=
  jointWeight half quarter a b c kappa tau z row (d, ⟨s.val+1,by omega⟩) -
    alpha^(s.val+1) * jointWeight half quarter a b c kappa tau z row (d,0)

lemma pair_block (h alpha : F) (d : Fin 256) (s : Fin 3) (w : Fin 4 → F) :
    (∑ slot : Fin 4, (h * indexedPair alpha d s (d,slot)) * w slot) =
      h * (w ⟨s.val+1,by omega⟩ - alpha^(s.val+1) * w 0) := by
  simp [indexedPair, indexedBasis, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    mul_sub, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]

def normalizedPair (alpha : F) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 256) (s : Fin 3) : Index256 → F :=
  fun i => normalized t ht noneOne d i.1 * indexedPair alpha i.1 s i

theorem normalized_observation_sum (half quarter a b c kappa tau alpha : F)
    (z : Fin 10 → F) (row : ObservationRow) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) (d : Fin 256) (s : Fin 3) :
    rawObservation half quarter a b c kappa tau z
      (normalizedPair alpha t ht noneOne d s) row =
      ∑ i : Fin 256, normalized t ht noneOne d i *
        pairedWeight half quarter a b c kappa tau alpha z row i s := by
  rw [rawObservation_weighted]
  apply Finset.sum_congr rfl
  intro i _
  exact pair_block (normalized t ht noneOne d i) alpha i s
    (fun slot => jointWeight half quarter a b c kappa tau z row (i,slot))

/-- Every low-coordinate repair is retained for arbitrary source weights. -/
theorem normalized_observation_repair (half quarter a b c kappa tau alpha : F)
    (z : Fin 10 → F) (row : ObservationRow) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) (d : Fin 256) (s : Fin 3) :
    rawObservation half quarter a b c kappa tau z
      (normalizedPair alpha t ht noneOne d s) row =
      (pairedWeight half quarter a b c kappa tau alpha z row d s -
        pairedWeight half quarter a b c kappa tau alpha z row 0 s) -
      ∑ j : Fin 23, low t ht noneOne d j *
        (pairedWeight half quarter a b c kappa tau alpha z row ⟨j.val,by omega⟩ s -
          pairedWeight half quarter a b c kappa tau alpha z row 0 s) := by
  rw [normalized_observation_sum]
  exact normalized_weight_repair t ht noneOne d
    (fun i => pairedWeight half quarter a b c kappa tau alpha z row i s)

#print axioms pair_block
#print axioms normalized_observation_sum
#print axioms normalized_observation_repair
end
end AspisV8R19.R765NormalizedJointRepair
