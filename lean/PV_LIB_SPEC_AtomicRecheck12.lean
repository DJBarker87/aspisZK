import PV_LIB_SPEC_NativeRecheck12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_AtomicRecheck12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine
abbrev C := PV_LIB_SPEC_ScopeAllocationGap.C
abbrev before := PV_LIB_SPEC_ConcreteCaptures.state
def store (b : Bool) : Store Data :=
  ⟨fun _ => some (PV_LIB_SPEC_NativeConstructors.atomicBool b),8⟩
def loadFn : Data := match PV_THR2_F6.node125 with
  | .leaf (.call _ fn _ _ _) => fn | _ => .null
def entry (b : Bool) : PV_W1_LeafBoundary.Entry :=
  ⟨store b,7,[],[],[],loadFn,
    [PV_STX2_TypedReferences.reference ⟨7,50,[]⟩ .null,.null],0,[]⟩

/-- The actual retained lane-A v2 numeric load reads BOTH canonical constructor
values, and returns the corresponding bool. This closes the C9 value-format
conflict without changing the read-only table or assuming successful decode.
It is a local value graph, not the original129 caller or its world effects. -/
theorem load_constructor (b : Bool) :
    PV_LIB_A_AtomicReadsV2.boolean C (entry b) before = some (.boolean b) := by
  cases b <;> rfl

/-- A canonical false constructor is accepted by the source-correct ScopeData
image as well as v2's load decoder. There is one representation in both planes. -/
theorem shared_zero (word : PV_OWN2_Codec.Pointer) :
    PV_LIB_A_AtomicReadsV2.boolean C (entry false) before = some (.boolean false) ∧
    PV_LIB_SPEC_NativeBoolArc.image C PV_LIB_SPEC_ScopeAllocationGap.K before .scope
      (PV_LIB_SPEC_ScopeAllocationGap.atomic 1) (PV_LIB_SPEC_ScopeAllocationGap.atomic 1)
      (PV_THR2_ScopeData.value (PV_LIB_SPEC_ScopeAllocationGap.atomic 0)
        (PV_THR2_OwnInitPointerCodec.encode word) (PV_LIB_SPEC_NativeConstructors.atomicBool false)) =
      some (PV_LIB_SPEC_AllocationImages.scope word.val) :=
  ⟨load_constructor false,PV_LIB_SPEC_NativeConstructors.initial_scope before word⟩

#print axioms store
#print axioms loadFn
#print axioms entry
#print axioms load_constructor
#print axioms shared_zero
end PV_LIB_SPEC_AtomicRecheck12
