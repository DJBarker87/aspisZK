import R1Z.PV_RW_IteratorStateLoop
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_IteratorStateBound
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Q := aspis_core.field.QM31
abbrev Iter := core.slice.iter.Iter U32
variable [ExternalTypes]

def bounded (ops : ExternalFuns) (lambda : Q) : Nat → Iter → Q × Q → Result (Q × Q)
  | 0, _, _ => .div
  | fuel+1, iterator, state => do
    let flow ← @PV_RW_IteratorStateSource.body _ (PV_CurrentScaleInstall.selected ops) lambda iterator state
    match flow with
    | .done final => ok final
    | .cont (next,acc) => bounded ops lambda fuel next acc

theorem control (ops : ExternalFuns) (lambda : Q) (fuel : Nat) (iterator : Iter) (state : Q × Q) :
    bounded ops lambda fuel iterator state=
      PV_RW_NativeForSource.bounded (PV_RW_CompressNativeState.step ops lambda) fuel iterator state := by
  induction fuel generalizing iterator state with
  | zero => rfl
  | succ fuel ih =>
    rw [bounded,PV_RW_NativeForSource.bounded,
      @PV_RW_IteratorStateSource.control _ (PV_CurrentScaleInstall.selected ops) lambda iterator state]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro flow _
    cases flow with
    | done final => rfl
    | cont pair => exact ih pair.1 pair.2

theorem sufficient (ops : ExternalFuns) (lambda : Q) (values : Slice U32) (i : Nat) (state : Q × Q) :
    PV_RW_IteratorStateLoop.run ops lambda (⟨values,i⟩ : Iter) state=
      bounded ops lambda (values.val.length-i+1) (⟨values,i⟩ : Iter) state := by
  rw [PV_RW_IteratorStateLoop.control,control]
  exact PV_RW_NativeForBound.exact_fuel _ values i state

theorem arity16 (ops : ExternalFuns) (lambda : Q) (values : Array U32 16#usize) (state : Q × Q) :
    PV_RW_IteratorStateLoop.run ops lambda (⟨Array.to_slice values,0⟩ : Iter) state=
      bounded ops lambda 17 (⟨Array.to_slice values,0⟩ : Iter) state := by
  rw [PV_RW_IteratorStateLoop.control,control]
  exact PV_RW_NativeForBound.arity16 _ values state
#print axioms control
#print axioms sufficient
#print axioms arity16
end R1Z.PV_RW_IteratorStateBound
