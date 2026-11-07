import PV_THR2_LibrarySemantics_ArcClone
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f360
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_THR2_LibrarySemantics_ArcClone

/-- Descriptor-parametric strengthening of W1's existing full-reply contract.
The exact native reply is unchanged on every branch. -/
def PostFrame {E : Type} (C : Carrier OWNER Data) (e : PV_W1_LeafBoundary.Entry)
    (H : PV_W1_OwnerNativeFrame.Backend E) (w : OWNER) (events : List E)
    (changes : Address → Option Data) (v : Valid C e w) : Prop :=
  PV_W1_ArgumentEffects.Post C e H w events changes ∧
  ∀ result, (PV_THR2_OwnUniformResourceHandler.lift H
    (.child e.callee e.store.nextActivation e.arguments) w).answer = .returned (.ok result) →
    Returned C e w v (PV_THR2_OwnUniformResourceHandler.lift H
      (.child e.callee e.store.nextActivation e.arguments) w) changes result

theorem contract_frame {E : Type} (C : Carrier OWNER Data) (e : PV_W1_LeafBoundary.Entry)
    (H : PV_W1_OwnerNativeFrame.Backend E) (w : OWNER) (events : List E)
    (effects : PV_W1_LeafBoundary.Entry → OWNER → Address → Option Data)
    (pre : PV_W1_ClosedLeaves.Pre e w)
    (arcClone : Fact C e H w (effects e w)) (v : Valid C e w) :
    PostFrame C e H w events (effects e w) v :=
  ⟨PV_W1_ArgumentEffects.full_reply C e H w events (effects e w) pre,arcClone v⟩

/-- The stronger leaf theorem implies W1's descriptor-parametric contract;
no change to its existing closure or descriptor is needed. -/
theorem implies_generic {E : Type} (C : Carrier OWNER Data) (e : PV_W1_LeafBoundary.Entry)
    (H : PV_W1_OwnerNativeFrame.Backend E) (w : OWNER) (events : List E)
    (changes : Address → Option Data) (v : Valid C e w)
    (post : PostFrame C e H w events changes v) :
    PV_W1_ArgumentEffects.Post C e H w events changes := post.1

/-- At W1's original f270 descriptor this also implies its published wrapper,
including fresh OWNER places. -/
theorem implies_W1 {E : Type} (C : Carrier OWNER Data) (e : PV_W1_LeafBoundary.Entry)
    (H : PV_W1_OwnerNativeFrame.Backend E) (w : OWNER) (args : List Data)
    (events : List E) (changes : Address → Option Data)
    (v : Valid C (PV_W1_NativeLeaves.entry360 e args) w)
    (pre : PV_W1_ClosedLeaves.Pre e w)
    (post : PostFrame C (PV_W1_NativeLeaves.entry360 e args) H w events changes v) :
    PV_W1_NativeLeaves.Post360 C e H w args events changes :=
  ⟨post.1,PV_W1_OwnerWellFormed.fresh_callee w e.store.nextActivation pre⟩

#print contract_frame
#print axioms contract_frame
#print axioms implies_generic
#print axioms implies_W1
end PV_FN_THREAD_f360
