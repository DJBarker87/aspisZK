import AspisV8R19.HighWitnessTransport

/-! Transport the complete fixed witness, including its G boundary term,
through a ring embedding. This does not assert source challenge support. -/
namespace AspisR19.HighWitnessFieldTransport
open RootCertificate SparseHighWitness HighRepairInvariant BetaUniformCorrection
noncomputable section
variable {F : Type*} [CommRing F]

def observed (f : M →+* F) (q : Index 32 → F) (row : Nat) : F :=
  if row<3 then ∑ i, q i*f (e row i)
  else if row<10 then coefficient (sourceKernel 32 (row-3) (f 536870912)) q (fun i => f (wr i))
  else coefficient (sourceKernel 32 (row-10) (f 536870912)) q (fun i => f (wg i))

theorem map_observed (f : M →+* F) (q : Index 32 → M) (row : Nat) :
    observed f (fun i => f (q i)) row = f (HighWitnessTransport.observed q row) := by
  unfold observed HighWitnessTransport.observed
  split_ifs <;>
    simp only [coefficient,sourceKernel,map_sum,map_mul,apply_ite,map_zero]

theorem observed_high (f : M →+* F) (q v : Index 32 → F)
    (same : ∀ i, 22 ≤ i.1.val → q i=v i) (row : Nat) :
    observed f q row=observed f v row := by
  unfold observed
  split_ifs
  · apply point_high 22 q v _ same
    intro i hi; rw [HighWitnessTransport.e_low row i hi,map_zero]
  · apply coefficient_high 22 _ _ q v _ same
    intro i hi; rw [HighWitnessTransport.wr_low i hi,map_zero]
  · apply coefficient_high 22 _ _ q v _ same
    intro i hi; rw [HighWitnessTransport.wg_low i hi,map_zero]

def matrix (f : M →+* F) (q : Fin 13 → Index 32 → F) : Matrix (Fin 13) (Fin 13) F :=
  fun i j => observed f (q j) (ResidualModel.selectedRow i)

theorem matrix_equal (f : M →+* F) (q : Fin 13 → Index 32 → F)
    (same : ∀ j i, 22 ≤ i.1.val → q j i=f (column (7:M) (degree j) (slot j) i)) :
    matrix f q=SparseHighWitness.matrix.map f := by
  funext i j
  change observed f (q j) _ = f (SparseHighWitness.matrix i j)
  rw [observed_high f _ _ (same j),map_observed,HighWitnessTransport.direct_observed]
  rfl

theorem repaired_det_ne_zero (f : M →+* F) (hf : Function.Injective f)
    (q : Fin 13 → Index 32 → F)
    (same : ∀ j i, 22 ≤ i.1.val → q j i=f (column (7:M) (degree j) (slot j) i)) :
    (matrix f q).det ≠ 0 := by
  rw [matrix_equal f q same]
  change (f.mapMatrix SparseHighWitness.matrix).det ≠ 0
  rw [← f.map_det]
  intro h
  apply HighWitnessData.model_det_ne_zero
  apply hf
  simpa only [map_zero] using h

#print axioms map_observed
#print axioms observed_high
#print axioms matrix_equal
#print axioms repaired_det_ne_zero
end
end AspisR19.HighWitnessFieldTransport
