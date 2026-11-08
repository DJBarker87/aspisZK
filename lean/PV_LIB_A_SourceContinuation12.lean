import PV_LIB_A_Continuation12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_SourceContinuation12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

/-- Retained source phases are never reset by a later source-frontier segment. -/
def steps (cost : State → Nat) (q : SourceState) : Nat :=
  match q.applied with | none => cost q.base | some _ => 0

def after (finish : State → State) (q : SourceState) : SourceState :=
  match q.applied with | none => ⟨finish q.base,none⟩ | some _ => q

/-- Lift a checked source-frontier segment over the phase-bearing machine.
A pending native write remains pending with the identical written store/token. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (cost : State → Nat) (finish : State → State)
    (certificate : ∀ q, advance C K P resources encode H values (cost q) ⟨q,none⟩ = ⟨finish q,none⟩)
    (q : SourceState) :
    advance C K P resources encode H values (steps cost q) q = after finish q := by
  rcases q with ⟨q,phase⟩
  cases phase with
  | none => exact certificate q
  | some phase => rfl

#print axioms steps
#print axioms after
#print axioms run
end PV_LIB_A_SourceContinuation12
