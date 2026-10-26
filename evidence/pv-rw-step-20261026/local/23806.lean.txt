import R1Z.PV_RW_CompressPowerChunk
import R1Z.PV_RW_CompressNativePower
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressPowerChunks16
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
abbrev Q := ProverRwFull.aspis_core.field.QM31
variable [ProverRwFull.ExternalTypes]

-- Symbolic 8+8 aggregation of the final power; no concrete recurrence reduction.
theorem split (ops : ProverRwFull.ExternalFuns) (values : Array U32 16#usize)
    (lambda out power : Q) :
    mapResult Prod.snd (PV_RW_IteratorStateLoop.run ops lambda
      (⟨Array.to_slice values,0⟩ : PV_RW_IteratorStateLoop.Iter) (out,power))=(do
      let middle ← PV_RW_CompressPowerFold.powerRun lambda 8 power
      PV_RW_CompressPowerFold.powerRun lambda 8 middle) := by
  rw [PV_RW_CompressNativePower.arity16]
  exact PV_RW_CompressPowerChunk.append lambda 8 8 power
#print axioms split
end R1Z.PV_RW_CompressPowerChunks16
