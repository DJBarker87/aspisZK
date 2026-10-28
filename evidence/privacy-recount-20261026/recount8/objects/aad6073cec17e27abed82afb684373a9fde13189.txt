import R1Z.PV_RW_NativeForList
import R1Z.PV_RW_CompressClosed
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressNativeControl
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Q := aspis_core.field.QM31
variable [ExternalTypes]

-- Composition of the emitted arithmetic step and emitted iterator step using
-- the actual Aeneas Std loop. Source association of the original whole helper
-- remains a separately named obligation; this is not defined as its output.
def source (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : Q) : Result Q := do
  let complex ← (PV_CurrentScaleInstall.selected ops).op61 tag
  let initial ← (PV_CurrentScaleInstall.selected ops).op66 complex
  let iterator ← SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter values
  let state ← PV_RW_NativeForSource.run (fun value state =>
    @PV_RW_CompressEmission.generated.shipped_step _ (PV_CurrentScaleInstall.selected ops)
      state.1 state.2 value lambda) iterator (initial,lambda)
  ok state.1

theorem listRun (step : U32 → Q × Q → Result (Q × Q)) (values : List U32) (state : Q × Q) :
    PV_RW_ResultListRun.run step values state=PV_RW_CompressStep.run step values state := by
  induction values generalizing state with
  | nil => rfl
  | cons value tail ih =>
    change (do let next ← step value state; PV_RW_ResultListRun.run step tail next)=_
    change _=(do let next ← step value state; PV_RW_CompressStep.run step tail next)
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next _
    exact ih next

theorem closed (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : Q) :
    source ops tag values lambda=PV_RW_CompressClosed.compress tag values lambda := by
  unfold source
  rw [PV_RW_CompressLiftSelectors.complex]
  simp only [bind_tc_ok,PV_RW_CompressLiftSelectors.quartic]
  rw [PV_RW_IteratorSource.start]
  simp only [bind_tc_ok]
  rw [PV_RW_NativeForList.initial,listRun,PV_RW_CompressClosedFold.emitted_closed]
  rfl

theorem owned (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : Q) :
    source ops tag values lambda=PV_RW_CompressClosed.owned tag values lambda :=
  (closed ops tag values lambda).trans (PV_RW_CompressClosed.owned_equal tag values lambda)

theorem arity16 (ops : ExternalFuns) (tag : U32) (values : Array U32 16#usize) (lambda : Q) :
    source ops tag (Array.to_slice values) lambda=
      PV_RW_CompressClosed.owned tag (Array.to_slice values) lambda := owned ops tag _ lambda
#print axioms listRun
#print axioms closed
#print axioms owned
#print axioms arity16
end R1Z.PV_RW_CompressNativeControl
