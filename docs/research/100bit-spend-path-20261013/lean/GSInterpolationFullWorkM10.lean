import GSInterpolationMatrixWorkM10
import GSInterpolationNormalizationWorkM10
import GSDenseKernelResourcesM10

/-! Matrix construction, complete kernel-basis production (not just RREF),
first-vector selection and post-kernel normalization in one costed call.
Both work and cumulative copying slots from the kernel are retained. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.GSInterpolationFullWorkM10
open CompPoly CompPoly.GuruswamiSudan
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

def eval (D : Nat) (basis : Array CBivariate.Monomial) (points : Array (K × K)) :
    Option (CBivariate K) × Nat :=
  let M := GSInterpolationMatrixWorkM10.matrix D basis points
  let k := GSDenseKernelResourcesM10.eval M.1
  let cost := M.2+k.2.work+k.2.allocated+1
  match k.1 with
  | none => (none,cost)
  | some v =>
    let p := GSInterpolationNormalizationWorkM10.normalize D basis v
    (p.1,cost+p.2)

def params (D : Nat) : GSInterpParams := ⟨1,3,D⟩

theorem value (D : Nat) (basis : Array CBivariate.Monomial) (points : Array (K × K))
    (p : GSInterpParams) (h : p.multiplicity = 3) :
    (eval D basis points).1 = denseInterpolateWithBasisAndKernel (denseLinearKernelContext K)
      basis points p := by
  simp only [eval, GSDenseKernelResourcesM10.value, GSInterpolationMatrixWorkM10.value,
    GSInterpolationNormalizationWorkM10.normalize_value,
    denseInterpolateWithBasisAndKernel, interpolationMatrixOnBasis,
    denseLinearKernelContext, DenseMatrix.homogeneousWitnessInPlace_eq, h]
  split <;> rename_i hx <;> simp only [hx, Option.bind_none, Option.bind_some] <;> rfl

def kernelBudget (r c : Nat) : Nat :=
  16*(GSDenseKernelResourcesM10.iterations r c+r+c+1)*(r*c+r+c+1)

def budget (D points basis : Nat) : Nat :=
  100*(points+1)^2+(6*points*basis)*(RRRowConstructionWorkM10.termTariff D+6)+2+
    2*kernelBudget (6*points) basis+1+
    (5*basis+basis*GSInterpolationNormalizationWorkM10.addTariff D+5)

theorem kernel_bound (D : Nat) (basis : Array CBivariate.Monomial) (points : Array (K × K)) :
    GSDenseKernelResourcesM10.budget (GSInterpolationMatrixWorkM10.matrix D basis points).1 =
      kernelBudget (6*points.size) basis.size := by
  simp only [GSDenseKernelResourcesM10.budget, GSDenseKernelResourcesM10.capacity,
    GSInterpolationMatrixWorkM10.rows, GSInterpolationMatrixWorkM10.cols,
    GSInterpolationMatrixWorkM10.stored_cells, kernelBudget]

theorem work (D : Nat) (basis : Array CBivariate.Monomial) (points : Array (K × K)) :
    (eval D basis points).2 ≤ budget D points.size basis.size := by
  have hM := GSInterpolationMatrixWorkM10.work D basis points
  have hk := GSDenseKernelResourcesM10.work (GSInterpolationMatrixWorkM10.matrix D basis points).1
  have ha := GSDenseKernelResourcesM10.allocation (GSInterpolationMatrixWorkM10.matrix D basis points).1
  rw [kernel_bound] at hk ha
  simp only [eval]
  split
  · dsimp only
    unfold budget
    omega
  · rename_i v hv
    have hv' : DenseMatrix.homogeneousWitness (GSInterpolationMatrixWorkM10.matrix D basis points).1 = some v := by
      rw [← GSDenseKernelResourcesM10.value]
      exact hv
    have hs := DenseMatrix.homogeneousWitness_width hv'
    change v.size = (GSInterpolationMatrixWorkM10.matrix D basis points).1.cols at hs
    rw [GSInterpolationMatrixWorkM10.cols] at hs
    have hp := GSInterpolationNormalizationWorkM10.normalize_work D basis v
    rw [hs] at hp
    dsimp only
    unfold budget
    omega

#print axioms value
#print axioms kernel_bound
#print axioms work
end AspisR1.GSInterpolationFullWorkM10
end
