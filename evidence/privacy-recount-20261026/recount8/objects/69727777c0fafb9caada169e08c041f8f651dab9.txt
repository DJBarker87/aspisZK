import R1Z.PV_RW_CompressNativeControl
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressNativeState
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Q := aspis_core.field.QM31
variable [ExternalTypes]

def step (ops : ExternalFuns) (lambda : Q) (value : U32) (state : Q × Q) : Result (Q × Q) :=
  @PV_RW_CompressEmission.generated.shipped_step _ (PV_CurrentScaleInstall.selected ops)
    state.1 state.2 value lambda

theorem whole_state (ops : ExternalFuns) (values : Slice U32) (lambda : Q) (state : Q × Q) :
    PV_RW_NativeForSource.run (step ops lambda) (⟨values,0⟩ : PV_RW_NativeForSource.Iter) state=
      PV_RW_CompressClosedFold.owned values.val lambda state := by
  rw [PV_RW_NativeForList.initial,PV_RW_CompressNativeControl.listRun]
  change PV_RW_CompressStep.run (fun value state =>
    @PV_RW_CompressEmission.generated.shipped_step _ (PV_CurrentScaleInstall.selected ops)
      state.1 state.2 value lambda) values.val state=_
  rw [PV_RW_CompressClosedFold.emitted_closed,PV_RW_CompressClosedFold.owned_equal]

theorem bounded_state (ops : ExternalFuns) (values : Slice U32) (lambda : Q) (state : Q × Q) :
    PV_RW_NativeForSource.bounded (step ops lambda) (values.val.length+1)
      (⟨values,0⟩ : PV_RW_NativeForSource.Iter) state=
      PV_RW_CompressClosedFold.owned values.val lambda state := by
  have bound := PV_RW_NativeForBound.exact_fuel (step ops lambda) values 0 state
  simp only [Nat.sub_zero] at bound
  exact bound.symm.trans (whole_state ops values lambda state)

theorem arity16 (ops : ExternalFuns) (values : Array U32 16#usize) (lambda : Q) (state : Q × Q) :
    PV_RW_NativeForSource.bounded (step ops lambda) 17
      (⟨Array.to_slice values,0⟩ : PV_RW_NativeForSource.Iter) state=
      PV_RW_CompressClosedFold.owned values.val lambda state := by
  rw [← PV_RW_NativeForBound.arity16]
  exact whole_state ops (Array.to_slice values) lambda state
#print axioms whole_state
#print axioms bounded_state
#print axioms arity16
end R1Z.PV_RW_CompressNativeState
