import PV_FN_THREAD_f6DeliveryRegression
import PV_FN_THREAD_f6ProviderInterfaces
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6DeliveryInterfaces
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces

/-- The still-open125 dependency at the corrected delivery boundary. Pre and
value/frame clauses are literally the previous consumer interface, using the
provider's NonNull root and emitted aggregate definitions by name. No provider
Pre/Post contract exists yet in W4's f125_Row. The historical interface remains
available for its accepted diagnostics and local returned-case joins. -/
def f125 {E : Type} (M : Machine E) : Prop :=
  ∀ (x : Entry E) (a : Nat) (capture : Data) (p : Address)
    (strong weak payload : Data),
    x.body = PV_THR2_F125.live →
    x.args = [PV_THR2_ScopeCaptureWrap.value a capture] → EntryValid x →
    At M.carrier x.store ⟨a,2,[0]⟩ (PV_FN_THREAD_f222_EntryOwned.root p) →
    At M.carrier x.store p (PV_THR2_KeyValues.pack
      PV_THR2_Packet124Aggregate13.source.2.2.1 [strong,weak,payload]) →
    PV_FN_THREAD_f6Joins.FullPost M x (fun s _ result =>
      At M.carrier s ⟨a,2,[0]⟩ (PV_FN_THREAD_f222_EntryOwned.root p) ∧
      (∃ strong' weak', At M.carrier s p (PV_THR2_KeyValues.pack
        PV_THR2_Packet124Aggregate13.source.2.2.1 [strong',weak',payload])) ∧
      (M.control.variant result = some 0 ∨ M.control.variant result = some 1))

/-- Explicit relation to the historical statement. This implication asserts
neither interface is inhabited and earns no125 or f6 closure credit. -/
theorem of_legacy {E : Type} (M : Machine E)
    (old : PV_FN_THREAD_f6ProviderInterfaces.f125 M) : f125 M := by
  intro x a capture p strong weak payload body args valid scope backing
  exact PV_FN_THREAD_f6DeliveryRegression.restrict_full_post M x _
    (old x a capture p strong weak payload body args valid scope backing)

#print axioms f125
#print axioms of_legacy
end PV_FN_THREAD_f6DeliveryInterfaces
