import R1Z.PV_RW_CompressNativeState
import R1Z.PV_RW_CompressClosedTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressNativeTotal
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Q := aspis_core.field.QM31
variable [ExternalTypes]

theorem state (ops : ExternalFuns) (values : Slice U32) (lambda : Q) (initial : Q × Q) :
    ∃ final, PV_RW_NativeForSource.run (PV_RW_CompressNativeState.step ops lambda)
      (⟨values,0⟩ : PV_RW_NativeForSource.Iter) initial=ok final := by
  rw [PV_RW_CompressNativeState.whole_state,← PV_RW_CompressClosedFold.owned_equal]
  exact PV_RW_CompressClosedTotal.fold values.val lambda initial

theorem output (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : Q) :
    ∃ final, PV_RW_CompressNativeControl.source ops tag values lambda=ok final := by
  rw [PV_RW_CompressNativeControl.closed]
  exact PV_RW_CompressClosedTotal.compress tag values lambda

theorem independent (left right : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : Q) :
    PV_RW_CompressNativeControl.source left tag values lambda=
      PV_RW_CompressNativeControl.source right tag values lambda := by
  rw [PV_RW_CompressNativeControl.closed,PV_RW_CompressNativeControl.closed]
#print axioms state
#print axioms output
#print axioms independent
end R1Z.PV_RW_CompressNativeTotal
