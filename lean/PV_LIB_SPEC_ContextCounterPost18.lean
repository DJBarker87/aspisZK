import PV_LIB_SPEC_ContextCounter18
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ContextCounterPost18
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)

/-- Full behavior plus the unchanged row-specific source frame. This helper
changes the reference machine/frontier, not the entry domain or frame facts. -/
def Post (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (finish : PV_LIB_SPEC_ContextMachine18.Finish) (entry : State) (frame : State → Prop)
    (issued : List Issued) (consumed : List Context) (candidate : Nat → Execution) : Prop :=
  let m := PV_LIB_SPEC_ContextMachine18.source cut p
  let initial := PV_LIB_SPEC_ContextMachine18.start entry issued consumed
  PV_LIB_SPEC_ContextCounter18.Behavior m finish initial candidate ∧
  ∀ k, (∀ j, j<k → ¬ PV_LIB_SPEC_ContextMachine18.Boundary m finish initial candidate j) →
    ¬ PV_LIB_SPEC_Frontier.Aborts (candidate k).state → frame (candidate k).state

def ordinary (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (body : PV_STX2_SliceSyntax.Program) (i : PV_LIB_SPEC_Row.Input)
    (issued : List Issued) (consumed : List Context) (candidate : Nat → Execution) : Prop :=
  Post cut p OwnComplete (PV_LIB_SPEC_Row.entry body i)
    (PV_LIB_SPEC_ThreadRow.Frame (runtime p) i) issued consumed candidate

#print axioms Post
#print axioms ordinary
end PV_LIB_SPEC_ContextCounterPost18
