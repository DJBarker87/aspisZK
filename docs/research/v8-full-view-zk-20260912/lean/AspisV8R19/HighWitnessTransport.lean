/- All low repairs preserve this fixed residual witness. Raw-kernel/source
   construction and the random-oracle law are separate obligations. -/
import AspisV8R19.HighWitnessNonzero

namespace AspisR19.HighWitnessTransport
open RootCertificate SparseHighWitness HighRepairInvariant BetaUniformCorrection
noncomputable section

theorem e_low (which : Nat) (i : Index 32) (hi : i.1.val<22) : e which i=0 := by
  have hr : 4*i.1.val+i.2.val<88 := by have := i.2.isLt; omega
  by_cases h0 : which=0
  · subst which; exact low0 ⟨_,hr⟩
  by_cases h1 : which=1
  · subst which; exact low1 ⟨_,hr⟩
  simpa [e,ew,h0,h1] using low2 ⟨4*i.1.val+i.2.val,hr⟩

theorem wr_low (i : Index 32) (hi : i.1.val<22) : wr i=0 := by
  simp [wr,e_low _ i hi]
theorem wg_low (i : Index 32) (hi : i.1.val<22) : wg i=0 := by
  have hr : 4*i.1.val+i.2.val<88 := by have := i.2.isLt; omega
  have h := low_hg ⟨4*i.1.val+i.2.val,hr⟩
  simp [wg,e_low _ i hi,h]

def observed (q : Index 32 → M) (row : Nat) : M :=
  if row<3 then ∑ i, q i*e row i
  else if row<10 then coefficient (sourceKernel 32 (row-3) (536870912:M)) q wr
  else coefficient (sourceKernel 32 (row-10) (536870912:M)) q wg

theorem direct_observed (j : Fin 13) (row : Nat) :
    observed (column (7:M) (degree j) (slot j)) row = observation row j := by
  simp only [observed,observation,column_point,column_coefficient]

theorem observed_high (q v : Index 32 → M)
    (same : ∀ i, 22 ≤ i.1.val → q i=v i) (row : Nat) :
    observed q row=observed v row := by
  unfold observed
  split_ifs
  · exact point_high 22 q v _ same (e_low row)
  · exact coefficient_high 22 _ _ q v _ same wr_low
  · exact coefficient_high 22 _ _ q v _ same wg_low

def matrix (q : Fin 13 → Index 32 → M) : Matrix (Fin 13) (Fin 13) M :=
  fun i j => observed (q j) (ResidualModel.selectedRow i)

theorem matrix_equal (q : Fin 13 → Index 32 → M)
    (same : ∀ j i, 22 ≤ i.1.val → q j i=column (7:M) (degree j) (slot j) i) :
    matrix q=SparseHighWitness.matrix := by
  funext i j
  exact (observed_high _ _ (same j) _).trans (direct_observed j _)

theorem repaired_det_ne_zero (q : Fin 13 → Index 32 → M)
    (same : ∀ j i, 22 ≤ i.1.val → q j i=column (7:M) (degree j) (slot j) i) :
    (matrix q).det ≠ 0 := by
  rw [matrix_equal q same]
  exact HighWitnessData.model_det_ne_zero

#print axioms e_low
#print axioms wr_low
#print axioms wg_low
#print axioms direct_observed
#print axioms observed_high
#print axioms matrix_equal
#print axioms repaired_det_ne_zero
end
end AspisR19.HighWitnessTransport
