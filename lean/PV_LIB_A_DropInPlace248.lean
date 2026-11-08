import PV_LIB_A_ExactDestructMethods
import PV_LIB_A_TypedDropSource
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_DropInPlace248
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_A_CellSetBegin PV_LIB_A_TypedDestruct

/-- ptr::drop_in_place's exact emitted T and Destruct argument. Resolving
UntrackedDestruct uses T; it is never replaced by an empty destructor. -/
def resolution (fn : Data) : Option Resolution := do
  if PV_THR2_OffPath.functionId fn = some 248 then
    let normalized ← normalize 64 fn
    let d ← destructor normalized
    PV_LIB_A_ExactDestructMethods.resolve d.type d.witness
  else none

structure Site where
  waiting : PV_STX2_Native.Waiting Data
  reference : Data
  destructor : Resolution

/-- The original pointer is retained, including its metadata. No temporary
copy of T is made, and the source allocation is not freed by this operation. -/
def select (c : Config) : Option Site := do
  match c.frame.completed with
  | some _ => none
  | none =>
    let wait ← c.frame.waiting
    match wait.request with
    | .child fn _ [reference] =>
      let d ← resolution fn
      pure ⟨wait,reference,d⟩
    | _ => none

def forwardedWait (c : Config) (site : Site) (fn : Data) : PV_STX2_Native.Waiting Data :=
  ⟨.child (.object [("Regular",fn)])
    (match site.waiting.request with | .child _ a _ => a | _ => c.frame.activation)
    [site.reference],site.waiting.action,site.waiting.unwind⟩

/-- Named documented-semantics forwarding of248 onto the selected typed glue.
The original pointer, action and cleanup are retained; no allocation is freed. -/
def PV_THR2_LibrarySemantics_DropInPlace248 (c : Config) (site : Site) : Config :=
  match site.destructor with
  | .noop => c
  | .call fn =>
    let wait := forwardedWait c site fn
    {c with frame := {c.frame with waiting := some wait}}

theorem forwarded (c : Config) (site : Site) (fn : Data)
    (resolved : site.destructor = .call fn) :
    (PV_THR2_LibrarySemantics_DropInPlace248 c site).frame.waiting =
      some (forwardedWait c site fn) := by
  simp only [PV_THR2_LibrarySemantics_DropInPlace248,resolved]

theorem frame (c : Config) (site : Site) :
    (PV_THR2_LibrarySemantics_DropInPlace248 c site).store = c.store ∧
    (PV_THR2_LibrarySemantics_DropInPlace248 c site).callers = c.callers := by
  cases h : site.destructor <;> simp [PV_THR2_LibrarySemantics_DropInPlace248,h]

#print axioms forwardedWait
#print axioms resolution
#print axioms select
#print axioms PV_THR2_LibrarySemantics_DropInPlace248
#print axioms forwarded
#print axioms frame
end PV_LIB_A_DropInPlace248
