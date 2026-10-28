import R1Z.PV_RW_CompressClosedFold
import R1Z.PV_RW_CompressLiftSelectors
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressClosed
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Q := aspis_core.field.QM31

-- Fully closed arithmetic reference: these definitions have no ExternalFuns.
def compress (tag : U32) (values : Slice U32) (lambda : Q) : Result Q := do
  let state ← PV_RW_CompressClosedFold.fold values.val lambda
    (PV_RW_CompressLiftSelectors.initial tag,lambda)
  ok state.1

def owned (tag : U32) (values : Slice U32) (lambda : Q) : Result Q := do
  let state ← PV_RW_CompressClosedFold.owned values.val lambda
    (PV_RW_CompressLiftSelectors.initial tag,lambda)
  ok state.1

variable [ExternalTypes]

theorem source (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : Q) :
    @PV_RW_CompressIterator.compress _ (PV_CurrentScaleInstall.selected ops) tag values lambda =
      compress tag values lambda := by
  unfold PV_RW_CompressIterator.compress
  change (do
    let c ← (PV_CurrentScaleInstall.selected ops).op61 tag
    let out ← (PV_CurrentScaleInstall.selected ops).op66 c
    @PV_RW_CompressIterator.execute _ (PV_CurrentScaleInstall.selected ops)
      lambda values.val out lambda) = _
  rw [PV_RW_CompressLiftSelectors.complex]
  simp only [bind_tc_ok,PV_RW_CompressLiftSelectors.quartic]
  rw [PV_RW_CompressClosedFold.source_loop]
  rfl

theorem reference (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : Q) :
    @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops) tag values lambda =
      compress tag values lambda :=
  (@PV_RW_CompressIterator.reference _ (PV_CurrentScaleInstall.selected ops) tag values lambda).symm.trans
    (source ops tag values lambda)

theorem owned_equal (tag : U32) (values : Slice U32) (lambda : Q) :
    compress tag values lambda = owned tag values lambda := by
  unfold compress owned
  rw [PV_RW_CompressClosedFold.owned_equal]

theorem source_arity16 (ops : ExternalFuns) (tag : U32) (values : Array U32 16#usize) (lambda : Q) :
    @PV_RW_CompressIterator.compress _ (PV_CurrentScaleInstall.selected ops)
      tag (Array.to_slice values) lambda = owned tag (Array.to_slice values) lambda :=
  (source ops tag _ lambda).trans (owned_equal tag _ lambda)
#print axioms source
#print axioms reference
#print axioms owned_equal
#print axioms source_arity16
end R1Z.PV_RW_CompressClosed
