import PV_FN_THREAD_f170_ActualNativeFrames
set_option autoImplicit false
noncomputable section
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame

/- Definitions moved verbatim from the accepted world-facet module, so the
active Statement can inventory the ADOPTED thread-24 facts without a cycle. -/
def PV_THR2_LibrarySemantics_AsRef277World {E : Type}
    (H : Backend E) : Prop :=
  ∀ e w, let d := PV_W1_NativeLeaves.entry277 e e.arguments
    (PV_THR2_OwnUniformResourceHandler.lift H
      (.child d.callee d.store.nextActivation d.arguments) w).world = w

def PV_THR2_LibrarySemantics_OkOr278World {E : Type}
    (H : Backend E) : Prop :=
  ∀ e w, let d := PV_W1_NativeLeaves.entry278 e e.arguments
    (PV_THR2_OwnUniformResourceHandler.lift H
      (.child d.callee d.store.nextActivation d.arguments) w).world = w

def PV_THR2_LibrarySemantics_Branch279World {E : Type}
    (H : Backend E) : Prop :=
  ∀ e w, let d := PV_W1_NativeLeaves.entry279 e e.arguments
    (PV_THR2_OwnUniformResourceHandler.lift H
      (.child d.callee d.store.nextActivation d.arguments) w).world = w

namespace PV_FN_THREAD_f170
/-- Additional exact-function facets, inventoried separately; not an assumed
reachable invariant, a Store frame, or a replacement for DocumentedFacts. -/
structure DocumentedValueFacts {E : Type} (H : Backend E) : Prop where
  asRef277World : PV_THR2_LibrarySemantics_AsRef277World H
  okOr278World : PV_THR2_LibrarySemantics_OkOr278World H
  branch279World : PV_THR2_LibrarySemantics_Branch279World H

#print axioms DocumentedValueFacts
end PV_FN_THREAD_f170
