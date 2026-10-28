import R1Z.ProverRwP6BodyCandidate
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BasisCell38
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev MA := Array U32 28#usize

theorem shift (ops : ExternalFuns) (basis : MA) (k : Usize) :
    @host_sumcheck.interpolation_shift _ (ProverRwP6BodyCandidate.selected ops) basis k =
      AspisR1ProducerRelease47.predecessor basis k := by
  unfold host_sumcheck.interpolation_shift AspisR1ProducerRelease47.predecessor
  by_cases hz : k=0#usize
  · simp only [hz,↓reduceIte]
    change (Result.ok AspisR1ProducerRelease47.field.M31.ZERO : Result U32) = _
    rfl
  · simp only [hz,↓reduceIte]

def cell (basis : MA) (k : Usize) (j : U32) : Result MA := do
  let shifted ← AspisR1ProducerRelease47.predecessor basis k
  let m ← Array.index_usize basis k
  let product ← AspisR1ProducerRelease47.field.M31.mul m j
  let value ← AspisR1ProducerRelease47.field.M31.sub shifted product
  Array.update basis k value

/-- Complete Result equality at one descending coefficient update; the
source's predecessor read occurs before the in-place write. -/
theorem update (ops : ExternalFuns) (basis : MA) (k j : Usize) :
    @host_sumcheck.interpolation_basis_cell _ (ProverRwP6BodyCandidate.selected ops) basis k j =
      cell basis k (UScalar.cast .U32 j) := by
  unfold host_sumcheck.interpolation_basis_cell
  rw [shift]
  simp only [lift,bind_tc_ok]
  rfl

#print axioms shift
#print axioms update
end R1Z.PV_RunJoin_BasisCell38
