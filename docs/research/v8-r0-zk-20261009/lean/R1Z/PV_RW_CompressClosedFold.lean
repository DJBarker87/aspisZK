import R1Z.PV_RW_CompressConcreteBinding
import R1Z.PV_RW_CompressIterator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressClosedFold
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Q := aspis_core.field.QM31

def fold (values : List U32) (lambda : Q) (state : Q × Q) : Result (Q × Q) :=
  PV_RW_CompressStep.run (fun value state =>
    PV_RW_CompressConcrete.step state.1 state.2 value lambda) values state

def owned (values : List U32) (lambda : Q) (state : Q × Q) : Result (Q × Q) :=
  PV_RW_CompressStep.run (fun value state =>
    PV_RW_CompressConcrete.owned state.1 state.2 value lambda) values state

variable [ExternalTypes]

theorem emitted_closed (ops : ExternalFuns) (values : List U32) (lambda : Q) (state : Q × Q) :
    PV_RW_CompressStep.run (fun value state =>
      @PV_RW_CompressEmission.generated.shipped_step _ (PV_CurrentScaleInstall.selected ops)
        state.1 state.2 value lambda) values state = fold values lambda state := by
  apply PV_RW_CompressStep.run_congr
  intro value state
  exact PV_RW_CompressConcreteBinding.emitted_closed ops state.1 state.2 value lambda

theorem reference (ops : ExternalFuns) (values : List U32) (lambda : Q) (state : Q × Q) :
    fold values lambda state =
      @PV_CompressList.stateFold _ (PV_CurrentScaleInstall.selected ops) values lambda state :=
  (emitted_closed ops values lambda state).symm.trans
    (@PV_RW_CompressEmission.emitted_fold _ (PV_CurrentScaleInstall.selected ops) lambda values state)

theorem owned_equal (values : List U32) (lambda : Q) (state : Q × Q) :
    fold values lambda state = owned values lambda state := by
  simp only [fold,owned,PV_RW_CompressConcrete.current_owned]

theorem source_loop (ops : ExternalFuns) (values : List U32) (lambda out power : Q) :
    @PV_RW_CompressIterator.execute _ (PV_CurrentScaleInstall.selected ops) lambda values out power =
      (do let state ← fold values lambda (out,power); ok state.1) := by
  rw [@PV_RW_CompressIterator.fold _ (PV_CurrentScaleInstall.selected ops)]
  unfold PV_CompressList.fold
  rw [← reference ops]
#print axioms emitted_closed
#print axioms reference
#print axioms owned_equal
#print axioms source_loop
end R1Z.PV_RW_CompressClosedFold
