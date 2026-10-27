import R1Z.ProverRw18ContextJoin
import R1Z.PV_RW_CombinedBodyData
import R1Z.ProverRwDictionaryLayoutValues
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19SelectedProofSize
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

-- Only record projections are reduced here. The existing symbolic layout
-- theorem supplies the numeric value, with no source-byte equality assumed.
theorem original (ops : ExternalFuns) :
    (ProverRwP6BodyStore.selected (ProverRw18ContextJoin.original ops)).op242 = ok 57607#usize := by
  change (ProverRwDictionaryLayout.selected ops).op242 = ok 57607#usize
  exact ProverRwDictionaryLayoutValues.proof_bytes ops

theorem closed (ops : ExternalFuns) :
    (ProverRwP6BodyStore.selected (PV_RW_CombinedBodyData.closed ops)).op242 = ok 57607#usize := by
  change (ProverRwDictionaryLayout.selected ops).op242 = ok 57607#usize
  exact ProverRwDictionaryLayoutValues.proof_bytes ops

#print axioms original
#print axioms closed
end R1Z.ProverRw19SelectedProofSize
