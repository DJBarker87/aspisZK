import PV_LIB_SPEC_Native13
import PV_LIB_SPEC_ConcreteEntry
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Entry13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_AllocationImages
local instance : DecidableEq Address := Classical.decEq _

/-- Original entry with native TLS already initialized. This is permitted
entry data, not a claim to have executed the process's TLS initialization. -/
def slot : PV_LIB_SPEC_TlsBindings13.Slot := ⟨⟨0,20,[]⟩,65520⟩
def store : Store Data :=
  PV_STX2_Store.write PV_LIB_SPEC_ConcreteEntry.store slot.source (some (.boolean false))

/-- Only the physical components of the initial owner change. The native
Thread allocation is live48/8 with sparse bytes; stack/TLS and counter are
static memory, never fabricated source OWNER registrations. -/
def state : OWNER :=
  let old := PV_LIB_SPEC_ConcreteCaptures.state
  let thread := initialized 16384 (threadInner 1 0 0) old
  let tls := PV_LIB_SPEC_ThreadWords12.write thread 65496 16400
  let counter := PV_LIB_SPEC_ThreadWords12.write tls PV_LIB_SPEC_ThreadId13.counterOffset 1
  {counter with world := {counter.world with
    memory := fun address => if address=slot.physical then some 0 else counter.world.memory address
    live := fun address => address=16384 || old.world.live address
    allocator := {counter.world.allocator with metadata := fun address =>
      if address=16384 then (some {bytes := 48,alignment := ._Align1Shl3}) else old.world.allocator.metadata address}}}

def input : OwnInit.Input := {PV_LIB_SPEC_ConcreteEntry.input with store := store,world := state}

/-- Initialized ACTIVE is checked against the SAME source store and physical
byte, without a TLS-value or decoder-success hypothesis. -/
theorem active : PV_LIB_SPEC_TlsBindings13.read slot PV_LIB_SPEC_ConcreteEntry.parameters
    ⟨{activation := 1,remaining := []},[],store⟩ state = some false := by
  change (do let Data.boolean b ← some (Data.boolean false) | none
             if some 0 = some (if b then 1 else 0) then some b else none) = some false
  rfl

/-- Actual native allocation metadata/liveness, independent of source OWNER
places. This strengthens session12's WORD-only TLS fixture. -/
theorem native_thread : state.world.allocator.metadata 16384 = some ⟨48,._Align1Shl3⟩ ∧
    state.world.live 16384 = true := by
  exact ⟨rfl,rfl⟩

theorem source_active : store.cells slot.source = some (.boolean false) :=
  PV_STX2_Store.write_same _ _ _

#print axioms slot
#print axioms store
#print axioms state
#print axioms input
#print axioms active
#print axioms native_thread
#print axioms source_active
end PV_LIB_SPEC_Entry13
