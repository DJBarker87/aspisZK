import GSDenseKernelBasisExtractionCost
import ExtractorFixedWidthResourcesM10

/-! Conservative copying tariffs around the full maintained kernel counter.
Every row-cell step reserves two complete backing-array copies; the extra
column/row allowance covers loop setup, pivot metadata and output vectors.
This deliberately pays the copying backend even when runtime sharing permits
the equivalent in-place backend to reuse memory. -/
set_option autoImplicit false
namespace AspisR1.GSDenseKernelResourcesM10
open CompPoly CompPoly.DenseMatrix ExtractorFixedWidthResourcesM10
variable {K : Type} [Field K] [BEq K]

def iterations (rows cols : Nat) : Nat :=
  (cols+1)*(rows+cols+(rows+1)*cols)+cols*(rows+1)*(cols+1)+1

def capacity (M : DenseMatrix K) : Nat := M.data.size+M.rows+M.cols+1

def eval (M : DenseMatrix K) : Option (Array K) × Events :=
  let r := homogeneousWitnessInPlaceFullCounted M
  let events := r.2+M.rows+M.cols+1
  (r.1, ⟨8*events,0,8*events,8*events*capacity M⟩)

def budget (M : DenseMatrix K) : Nat :=
  16*(iterations M.rows M.cols+M.rows+M.cols+1)*capacity M

theorem value (M : DenseMatrix K) : (eval M).1 = homogeneousWitness M := by
  simp only [eval, homogeneousWitnessInPlaceFullCounted_refines,
    homogeneousWitnessInPlace_eq]

theorem capacity_pos (M : DenseMatrix K) : 1 ≤ capacity M := by
  simp only [capacity]
  omega

theorem work (M : DenseMatrix K) : (eval M).2.work ≤ budget M := by
  have hc := homogeneousWitnessInPlaceFullCounted_cost_le M
  change _ ≤ iterations M.rows M.cols at hc
  have he : (homogeneousWitnessInPlaceFullCounted M).2+M.rows+M.cols+1 ≤
      iterations M.rows M.cols+M.rows+M.cols+1 := by omega
  change 8*_+0+8*_ ≤ _
  calc
    _ = 16*((homogeneousWitnessInPlaceFullCounted M).2+M.rows+M.cols+1) := by ring
    _ ≤ 16*(iterations M.rows M.cols+M.rows+M.cols+1) := Nat.mul_le_mul_left _ he
    _ ≤ _ := Nat.le_mul_of_pos_right _ (capacity_pos M)

theorem allocation (M : DenseMatrix K) : (eval M).2.allocated ≤ budget M := by
  have hc := homogeneousWitnessInPlaceFullCounted_cost_le M
  change _ ≤ iterations M.rows M.cols at hc
  change 8*_*capacity M ≤ _
  apply Nat.mul_le_mul_right
  have he : (homogeneousWitnessInPlaceFullCounted M).2+M.rows+M.cols+1 ≤
      iterations M.rows M.cols+M.rows+M.cols+1 := by omega
  exact Nat.mul_le_mul (by omega : 8 ≤ 16) he

theorem bit_bound (M : DenseMatrix K) (width tariff : Nat) :
    ((eval M).2.resources width tariff).bits ≤ budget M*(tariff+width) :=
  common_cap _ _ _ _ (work M) (allocation M)

theorem total_bound (M : DenseMatrix K) (width tariff : Nat) :
    ((eval M).2.resources width tariff).total ≤ budget M*(1+tariff+width) :=
  resources_total_bound _ _ _ _ (work M) (allocation M)

#print axioms value
#print axioms capacity_pos
#print axioms work
#print axioms allocation
#print axioms bit_bound
#print axioms total_bound
end AspisR1.GSDenseKernelResourcesM10
