import PV_LIB_SPEC_ActiveHistory18620
import PV_LIB_SPEC_NativeTargets18
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveTarget20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Context)
open PV_LIB_SPEC_EntryWorld18 (Entry)
open PV_LIB_SPEC_ActiveAdoption19 (history)
open PV_LIB_SPEC_ActiveOrigin18520 (origin)

/-- SPEC-C19 before: this diagnostic predicate incorrectly requested a
second source-issued context for an inner D877-contracted8248 computation. -/
abbrev Before := PV_LIB_SPEC_NativeTargets18.ActiveBeforeF6

/-- Correct source activation event at the enclosing source8162 origin.
The inner8248 reply and source effects are computed by the named C18 delivery,
not an invented origin, Store transformer or native-success hypothesis. -/
def Delivered (e : Entry) (a : Nat) : Prop :=
  PV_LIB_SPEC_ControlRuntime.ordinary (history e a 185).state =
    some (PV_LIB_A_F5CallbackStall16.config PV_LIB_SPEC_ActiveForward20.store176
      PV_LIB_A_F5FullEntry16.activation PV_LIB_A_F5FullEntry16.parents PV_LIB_SPEC_Entry13.slot.source,
      PV_LIB_A_F5CallbackStall16.wait PV_LIB_SPEC_ActiveForward20.store176 PV_LIB_SPEC_Entry13.slot.source) ∧
  (origin e a).site.statement = 8162 ∧
  (history e a 186).consumed = origin e a :: (history e a 185).consumed ∧
  (PV_W1_LeafBoundary.statusStore (history e a 186).state.current.status).cells
    PV_LIB_SPEC_Entry13.slot.source = some (.boolean true) ∧
  (history e a 186).state.current.world.world.memory PV_LIB_SPEC_Entry13.slot.physical = some 1

theorem delivered (e : Entry) (a : Nat) : Delivered e a :=
  ⟨PV_LIB_SPEC_ActiveOrigin18520.ordinary e a,(PV_LIB_SPEC_ActiveOrigin18520.site e a).2,
    PV_LIB_SPEC_ActiveHistory18620.consumed e a,PV_LIB_SPEC_ActiveHistory18620.source e a,
    PV_LIB_SPEC_ActiveHistory18620.physical e a⟩

/-- Checked mismatch of the old request on this actual original-history cut.
This is local specification repair, not a contradiction of the joint target. -/
theorem no_inner_origin (e : Entry) (a : Nat) (ctx : Context)
    (context : PV_LIB_SPEC_ResourceHistory.context (history e a 185)
      (PV_LIB_A_F5CallbackStall16.config PV_LIB_SPEC_ActiveForward20.store176
        PV_LIB_A_F5FullEntry16.activation PV_LIB_A_F5FullEntry16.parents PV_LIB_SPEC_Entry13.slot.source)
      (PV_LIB_A_F5CallbackStall16.wait PV_LIB_SPEC_ActiveForward20.store176 PV_LIB_SPEC_Entry13.slot.source) = some ctx) :
    ctx.site.statement ≠ 8248 := by
  rw [PV_LIB_SPEC_ActiveOrigin18520.context] at context
  have eq := Option.some.inj context
  rw [← eq]
  exact PV_LIB_SPEC_ActiveOrigin18520.not_inner e a

#print axioms Before
#print axioms Delivered
#print axioms delivered
#print axioms no_inner_origin
end PV_LIB_SPEC_ActiveTarget20
