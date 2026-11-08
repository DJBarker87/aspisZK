import PV_LIB_A_CellDestructFacts
import PV_LIB_A_WriterNumbering
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_DestructionNumbering
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_A_CellDestruct504
open PV_STX2_LiveNumbering

/-- Reuse the provider's generic push theorem at504's already reserved child
activation, and its monotonicity theorem for the local replacement writes.
The only counter identity here is a LOCAL write fact, never a row interface. -/
theorem cell_entry (C : Carrier OWNER Data) (c : Config) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) (selected : PV_LIB_A_CellDestruct504.Site) (unit : Data)
    (fn : Data) (args : List Data) (address : Address) (value : Data)
    (numbered : Numbered c) (waiting : c.frame.waiting = some selected.waiting)
    (request : selected.waiting.request = .child fn selected.activation args)
    (replacement : writeAddress C c.store address (some value) = some selected.prepared.store) :
    ∃ next, (PV_LIB_A_CellDestruct504.enter c w es stack selected unit).base.current.status = .running next ∧
      Numbered next := by
  let program : PV_STX2_SliceSyntax.Program := ⟨504,.null,.null,suffix selected.destructor⟩
  have pushed := push c program fn selected.activation args selected.waiting numbered waiting request
  have counter := PV_LIB_A_WriterNumbering.write_counter C c.store selected.prepared.store
    address (some value) replacement
  let store := write (write selected.prepared.store ⟨selected.activation,3,[]⟩
      (some selected.prepared.old)) ⟨selected.activation,0,[]⟩ (some unit)
  have mono : c.store.nextActivation ≤ store.nextActivation := by
    change c.store.nextActivation ≤ selected.prepared.store.nextActivation
    rw [counter]
  have transferred := PV_LIB_A_WriterNumbering.local_store _ store pushed mono
  exact ⟨_,rfl,transferred⟩

/-- A source-resolved typed Drop uses one fresh activation and retains the
actual saved parent. The generic waiting/stack monotonicity lemmas establish
all old-frame bounds under the enlarged counter. -/
theorem drop_entry (C : Carrier OWNER Data) (c : Config) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (selected : PV_LIB_A_TypedDropSource.Site) (numbered : Numbered c) :
    ∃ next, (PV_LIB_A_TypedDropSource.enter C c w es stack selected).base.current.status =
      .running next ∧ Numbered next := by
  refine ⟨_,rfl,?_⟩
  change c.store.nextActivation < c.store.nextActivation+1 ∧
    True ∧ StackBelow (c.store.nextActivation+1) c.store.nextActivation (c.frame :: c.callers)
  exact ⟨Nat.lt_succ_self _,trivial,numbered.1,
    waiting_mono numbered.2.1 (Nat.le_succ _),stack_mono numbered.2.2 (Nat.le_succ _)⟩

#print axioms cell_entry
#print axioms drop_entry
end PV_LIB_A_DestructionNumbering
