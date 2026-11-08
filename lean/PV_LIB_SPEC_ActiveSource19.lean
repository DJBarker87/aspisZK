import PV_LIB_SPEC_ActiveConsumption19
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveSource19
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Context)
open PV_LIB_A_F5CallbackStall16 (config)
open PV_LIB_SPEC_ActiveConsumption19 (delivered)

/-- Exact source output with the original waiting action. Administrative
return cells and the full counter remain; no equality of counters is imposed. -/
def store (s : Store Data) (a : Nat) (parents : List Frame) : Store Data :=
  write (write
    (write (config s a parents PV_LIB_SPEC_Entry13.slot.source).store
      PV_LIB_SPEC_Entry13.slot.source (some (.boolean true)))
    ⟨s.nextActivation,0,[]⟩ (some (.boolean false)))
    ⟨a,14,[]⟩ (some (.boolean false))

theorem status (ctx : Context) (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER) :
    (delivered ctx s a parents w).status =
      .running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 40},parents,
        store s a parents⟩ := rfl

/-- The real ACTIVE source cell is true after callback delivery; both return
cells are disjoint by local index, even without an activation-counter premise. -/
theorem cell (ctx : Context) (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER) :
    (PV_W1_LeafBoundary.statusStore (delivered ctx s a parents w).status).cells
      PV_LIB_SPEC_Entry13.slot.source = some (.boolean true) := by
  rw [status]
  change (store s a parents).cells PV_LIB_SPEC_Entry13.slot.source = _
  have dest : PV_LIB_SPEC_Entry13.slot.source ≠ (⟨a,14,[]⟩ : Address) := by
    intro eq; have index := congrArg Address.localIndex eq; cases index
  have result : PV_LIB_SPEC_Entry13.slot.source ≠ (⟨s.nextActivation,0,[]⟩ : Address) := by
    intro eq; have index := congrArg Address.localIndex eq; cases index
  simp only [store,write_other _ _ _ _ dest,write_other _ _ _ _ result,write_same]

/-- Complete older/caller-cell frame apart from the source effect and the
actual two return cells. This keeps all source bookkeeping visible. -/
theorem frame (s : Store Data) (a : Nat) (parents : List Frame) (q : Address)
    (tls : q ≠ PV_LIB_SPEC_Entry13.slot.source)
    (child : q ≠ (⟨s.nextActivation,0,[]⟩ : Address))
    (dest : q ≠ (⟨a,14,[]⟩ : Address)) :
    (store s a parents).cells q = (config s a parents PV_LIB_SPEC_Entry13.slot.source).store.cells q := by
  simp only [store,write_other _ _ _ _ dest,write_other _ _ _ _ child,write_other _ _ _ _ tls]

#print axioms store
#print axioms status
#print axioms cell
#print axioms frame
end PV_LIB_SPEC_ActiveSource19
