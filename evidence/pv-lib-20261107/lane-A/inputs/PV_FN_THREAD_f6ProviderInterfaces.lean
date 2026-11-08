import PV_FN_THREAD_f222_EntryOwned
import PV_FN_THREAD_f6InterfaceSites
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6ProviderInterfaces
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces

/-- The only consumer interface retained by thread-20 is the still-open125.
Arc representation is the provider's root, literally, including NonNull.
The source ArcInner aggregate kind is the provider's emitted source13 kind.
No consumer interface for124 or126 is declared here. -/
def f125 {E : Type} (M : Machine E) : Prop :=
  ∀ (x : Entry E) (a : Nat) (capture : Data) (p : Address)
    (strong weak payload : Data),
    x.body = PV_THR2_F125.live →
    x.args = [PV_THR2_ScopeCaptureWrap.value a capture] → EntryValid x →
    At M.carrier x.store ⟨a,2,[0]⟩ (PV_FN_THREAD_f222_EntryOwned.root p) →
    At M.carrier x.store p (PV_THR2_KeyValues.pack
      PV_THR2_Packet124Aggregate13.source.2.2.1 [strong,weak,payload]) →
    FullPost M x (fun s _ result =>
      At M.carrier s ⟨a,2,[0]⟩ (PV_FN_THREAD_f222_EntryOwned.root p) ∧
      (∃ strong' weak', At M.carrier s p (PV_THR2_KeyValues.pack
        PV_THR2_Packet124Aggregate13.source.2.2.1 [strong',weak',payload])) ∧
      (M.control.variant result = some 0 ∨ M.control.variant result = some 1))

#print axioms f125
end PV_FN_THREAD_f6ProviderInterfaces
