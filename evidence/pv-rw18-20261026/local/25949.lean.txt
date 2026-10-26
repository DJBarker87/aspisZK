import R1Z.ProverRw18FieldStateReference
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FieldSuffix
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning
variable [ProverRwFull.ExternalTypes]

theorem control (ops : ProverRwFull.ExternalFuns) (values : Slice U32) (i : Nat)
    (lambda : Q) (state : Q × Q) :
    PV_RW_IteratorStateLoop.run ops lambda (⟨values,i⟩ : core.slice.iter.Iter U32) state=
      PV_RW_CompressClosedFold.owned (values.val.drop i) lambda state := by
  rw [PV_RW_IteratorStateLoop.control,PV_RW_NativeForList.exact,
    PV_RW_CompressNativeControl.listRun]
  change PV_RW_CompressStep.run (fun value state =>
    @PV_RW_CompressEmission.generated.shipped_step _ (PV_CurrentScaleInstall.selected ops)
      state.1 state.2 value lambda) (values.val.drop i) state=_
  rw [PV_RW_CompressClosedFold.emitted_closed,PV_RW_CompressClosedFold.owned_equal]

theorem field (ops : ProverRwFull.ExternalFuns) (values : Slice U32) (i : Nat)
    (lambda out power : Raw) (hlambda : Canonical lambda) (hout : Canonical out) (hpower : Canonical power) :
    PV_RW_IteratorStateLoop.run ops (full lambda) (⟨values,i⟩ : core.slice.iter.Iter U32)
      (full out,full power)=ProverRw18FieldStateReference.reference (values.val.drop i) lambda out power := by
  rw [control]
  exact ProverRw18FieldStateReference.owned _ lambda out power hlambda hout hpower

#print axioms control
#print axioms field
end R1Z.ProverRw18FieldSuffix
