import PV_FN_SLICE_f4_ArrayBuiltins
import PV_FN_SLICE_f7_HandlerSpec
import PV_STX2_Source7QUniformInstalledHandler
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_RuntimeBindings
open PV_STX2_SliceMachine
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
/-- Named native Drop semantics on an arbitrary machine: the actual source
handler delegates every full Drop answer to its framed backend. No store-write,
success, counter or caller-frame hypothesis is contained in this predicate. -/
def DropSemantics (H : PV_FN_SLICE_f7_HandlerSpec.Handler) : Prop :=
  ∃ fallback : PV_W5_NativeFrame.Backend, ∀ (fn capture : Data) (w : OWNER),
    H (.drop fn capture) w = PV_STX2_Source7QUniformResourceHandler.lift fallback (.drop fn capture) w

theorem resource (H : PV_FN_SLICE_f7_HandlerSpec.Handler)
    (spec : PV_FN_SLICE_f7_HandlerSpec.Spec H) : DropSemantics H :=
  PV_FN_SLICE_f7_HandlerSpec.all_drops H spec

theorem installed_arrays (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (resources : PV_EVHB_OWNER.Resources) (encode : PV_EVHB_OWNER.Encode)
    {s : OWNER} {value : PV_STX2_Source7EntryOwned.Foundation}
    (entry : PV_STX2_Source7EntryOwned.Source7EntryOwned s value)
    (external : Nat → PV_STX_World.World → Reply PV_STX_World.World PV_RJ4IDB.NativeEvent Unit)
    (fallback : PV_W5_NativeFrame.Backend) :
    PV_FN_SLICE_f4_ArrayBuiltins.Spec
      (PV_STX2_Source7QUniformInstalledHandler.handler base ctrl resources encode entry external fallback) := by
  refine ⟨_,rfl⟩

/-- Bind Drop through the ENTIRE original installed handler stack, including
all existing source compiler-builtin and runtime-parts layers. -/
theorem installed_drop (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (resources : PV_EVHB_OWNER.Resources) (encode : PV_EVHB_OWNER.Encode)
    {s : OWNER} {value : PV_STX2_Source7EntryOwned.Foundation}
    (entry : PV_STX2_Source7EntryOwned.Source7EntryOwned s value)
    (external : Nat → PV_STX_World.World → Reply PV_STX_World.World PV_RJ4IDB.NativeEvent Unit)
    (fallback : PV_W5_NativeFrame.Backend) :
    DropSemantics
      (PV_STX2_Source7QUniformInstalledHandler.handler base ctrl resources encode entry external fallback) := by
  refine ⟨fallback,?_⟩
  intro fn capture w
  change PV_STX2_Source7QUniformResourceHandler.handler resources encode entry external fallback
    (.drop fn capture) w = _
  exact PV_FN_SLICE_f7_DropRuntime.drop resources encode entry external fallback fn capture w
#print axioms resource
#print axioms installed_arrays
#print axioms installed_drop
end PV_FN_SLICE_RuntimeBindings
