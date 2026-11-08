import PV_LIB_A_F5CallbackTrap16
import PV_FN_THREAD_f207_EffectsContract
import PV_FN_THREAD_f207_ConfinedFrame
import PV_LIB_SPEC_ActiveReplacement16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ActiveDispatch17
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
local instance : DecidableEq Data := Classical.decEq _

/-- Exact Adt56 callback resolution. FnDef18 forwarding remains separate.
The target is the emitted f207 and its actual unary tuple, not a unit stub. -/
def resolve (request : PV_STX2_Native.Request Data) : Option (Nat × Address) := do
  let .child fn a [closure,tuple] := request | none
  if fn = PV_THR2_RunTlsCallable.descriptors.1 ∧ closure = PV_LIB_A_F5FullEntry16.closure then
    let [reference] ← PV_THR2_FnOnceDispatch.tuple tuple | none
    let (pointer,_) ← PV_STX2_TypedReferences.decode reference
    pure (a,pointer)
  else none

def setter (a : Nat) (pointer : Address) : PV_STX2_Native.Request Data :=
  .child PV_FN_THREAD_f207.fn289 a (PV_FN_THREAD_f207.args pointer)

theorem actual (a : Nat) (pointer : Address) :
    resolve (PV_LIB_A_F5ClosurePending16.request a pointer) = some (a,pointer) := by
  have tuple : PV_THR2_FnOnceDispatch.tuple
      (PV_THR2_KeyValues.pack PV_THR2_RunTlsCallable.descriptors.2
        [PV_STX2_TypedReferences.reference pointer .null]) =
      some [PV_STX2_TypedReferences.reference pointer .null] := rfl
  simp only [resolve,PV_LIB_A_F5ClosurePending16.request,eq_self, and_self,ite_true,
    tuple]
  change (PV_STX2_TypedReferences.decode (PV_STX2_TypedReferences.reference pointer .null)).bind
    (fun pair => some (a,pair.1)) = some (a,pointer)
  rw [PV_STX2_TypedReferences.roundtrip]
  rfl


/-- Before: the context-bound environment gives pending, with identical world
and no events, at every exact callback. This is the model defect, not a
property of Active::enter in the binary. -/
theorem before (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : Resources)
    (s : Store Data) (a : Nat) (parents : List Frame) (pointer : Address) (w : OWNER) :
    PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources)
      (PV_LIB_SPEC_TlsCallable16.config s a parents PV_LIB_A_F5FullEntry16.closure pointer)
      (PV_LIB_A_F5ClosurePending16.request s.nextActivation pointer) w = some ⟨.pending,w,[]⟩ :=
  PV_LIB_A_F5CallbackObstruction16.answer_pending stack resources s a parents pointer w

/-- D727 TLS-only child interpretation at its actual callback boundary.
The source Cell reference and true argument are exactly f207's emitted ones.
Both native full reply and source-store write are supplied by named289 models;
malformed references remain unsupported. No result or Store delta is supplied. -/
def boundary (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (c : Config) (wait : PV_STX2_Native.Waiting Data) (w : OWNER) : Option (Prefix OWNER Event) := do
  let (a,pointer) ← resolve wait.request
  let r ← PV_LIB_SPEC_ReachedNative14.answer cut p c (setter a pointer) w
  let store ← PV_THR2_SourceStoreLibrary.PV_THR2_LibrarySemantics_CellReplace289
    (runtime p).carrier (PV_FN_THREAD_f207.args pointer) c.store w
  pure (PV_THR2_ChildBoundary.delivered (runtime p).carrier {c with store := store} wait r)

/-- All other resolutions retain the complete context-bound answer by name. -/
def answer (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (c : Config) (request : PV_STX2_Native.Request Data) (w : OWNER) : Option (Reply OWNER Event Data) :=
  match resolve request with
  | none => PV_LIB_SPEC_ReachedNative14.answer cut p c request w
  | some (a,pointer) => PV_LIB_SPEC_ReachedNative14.answer cut p c (setter a pointer) w

theorem agrees (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (c : Config) (request : PV_STX2_Native.Request Data) (w : OWNER)
    (other : resolve request = none) :
    answer cut p c request w = PV_LIB_SPEC_ReachedNative14.answer cut p c request w := by
  simp only [answer,other]

#print axioms resolve
#print axioms setter
#print axioms actual
#print axioms before
#print axioms boundary
#print axioms answer
#print axioms agrees
end PV_LIB_A_ActiveDispatch17
