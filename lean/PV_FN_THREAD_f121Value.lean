import PV_THR2_LibrarySemantics_AtomicUsizeNew
set_option autoImplicit false
set_option pp.piBinderNames true
noncomputable section
namespace PV_FN_THREAD_f121
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_THR2_LibrarySemantics_AtomicUsizeNew

def PostValue {E : Type} (C : Carrier OWNER Data) (e : PV_W1_LeafBoundary.Entry)
    (H : PV_W1_OwnerNativeFrame.Backend E) (w : OWNER) (events : List E)
    (changes : Address → Option Data) (n : Nat) : Prop :=
  PV_W1_ClosedLeaves.Post121 C e H w [.number n] events ∧
  PV_W1_ArgumentEffects.Post C (entry e n) H w events changes ∧
  Fact C e H w changes n

/-- Strengthened leaf summary at any actual call entry and any usize input.
No returned-case premise is required: all answers remain in Post121/Post. -/
theorem contract_value {E : Type} (C : Carrier OWNER Data) (e : PV_W1_LeafBoundary.Entry)
    (H : PV_W1_OwnerNativeFrame.Backend E) (w : OWNER) (events : List E)
    (changes : Address → Option Data) (n : Nat)
    (pre : PV_W1_ClosedLeaves.Pre e w)
    (atomicUsizeNew : Fact C e H w changes n) :
    PostValue C e H w events changes n :=
  ⟨PV_W1_ClosedLeaves.f121 C e H w [.number n] events pre,
   PV_W1_ArgumentEffects.full_reply C (entry e n) H w events changes pre,
   atomicUsizeNew⟩

theorem implies_W1 {E : Type} (C : Carrier OWNER Data) (e : PV_W1_LeafBoundary.Entry)
    (H : PV_W1_OwnerNativeFrame.Backend E) (w : OWNER) (events : List E)
    (changes : Address → Option Data) (n : Nat)
    (post : PostValue C e H w events changes n) :
    PV_W1_ClosedLeaves.Post121 C e H w [.number n] events := post.1

/-- Both provider calls4933/4945 have the exact descriptor used by the fact. -/
theorem provider_descriptors (e : PV_W1_LeafBoundary.Entry) (n : Nat) :
    PV_THR2_Packet124Children.fn7 = (entry e n).callee ∧
    PV_THR2_Packet124Children.fn9 = (entry e n).callee :=
  PV_FN_THREAD_f360Outcomes.counter_descriptors

#print contract_value
#print implies_W1
#print axioms contract_value
#print axioms implies_W1
#print axioms provider_descriptors
end PV_FN_THREAD_f121
