import PV_STX2_Source7ReachedReply
import PV_STX2_SliceToVecConstruct
set_option autoImplicit false
noncomputable section
namespace PV_STX2_Source7QBinding
open Aeneas Aeneas.Std PV_EVHB_OWNER PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_STX2_Source7EntryOwned
/-- Conditional on owner acceptance of the translator patch. The destination
is read from the generated Vec aggregate binding, never from erased values. -/
def destination : PV_STX2_Syntax.Place := match PV_STX2_SliceF21.node14 with
  | .leaf (.aggregateMove _ p _ _) => p
  | _ => .global 0
/-- Conditional on owner acceptance of the translator patch. Actual source
aggregate tag used to form the Vec in the to_vec result local. -/
def kind : Data := match PV_STX2_SliceF21.node14 with
  | .leaf (.aggregateMove _ _ tag _) => tag
  | _ => .null
/-- Conditional on owner acceptance of the translator patch. Native address
uses the reached to_vec activation and the generated aggregate destination. -/
def address (base : Carrier OWNER Data) {s : OWNER} {value : Foundation} (entry : Source7EntryOwned s value) : Option Address :=
  locate base
    (PV_STX2_Source7ReachedConstructor.config141 entry).store s
    (PV_STX2_Source7ReachedConstructor.config141 entry).frame.activation destination
/-- Conditional on owner acceptance of the translator patch. OWNER local
paths prepend the local index to its nested aggregate path. -/
def ownerPlace (p : Address) : PV_EVHB_OWNER.Place := ⟨p.activation,p.localIndex :: p.fields⟩
/-- Conditional on owner acceptance of the translator patch. q follows the
actual activation and generated LOCAL0 path; this does not yet register it. -/
theorem source_address (base : Carrier OWNER Data) {s : OWNER} {value : Foundation} (entry : Source7EntryOwned s value) :
    address base entry = some ⟨15,0,[]⟩ := by
  rfl
/-- Conditional on owner acceptance of the translator patch. Actual full
constructor success adopts the exact post-world and both return-local writes. -/
def returned {s : OWNER} {value : Foundation} (entry : Source7EntryOwned s value) (inner : Data) : Config :=
  let c := PV_STX2_Source7ReachedConstructor.config141 entry
  {c with
    store := write (write c.store ⟨16,0,[]⟩ (some inner)) ⟨15,8,[]⟩ (some inner),
    frame := {c.frame with waiting := none}}
/-- Conditional on owner acceptance of the translator patch. q is the actual
LOCAL0 path resolved at the reached activation, rather than a supplied place. -/
def q {s : OWNER} {value : Foundation} (entry : Source7EntryOwned s value) : PV_EVHB_OWNER.Place :=
  ownerPlace ⟨(PV_STX2_Source7ReachedConstructor.config141 entry).frame.activation,0,[]⟩
/-- Conditional on owner acceptance of the translator patch. Reached source
activation and emitted aggregate destination resolve to exactly q. -/
theorem resolved_q (base : Carrier OWNER Data) {s : OWNER} {value : Foundation}
    (entry : Source7EntryOwned s value) : (address base entry).map ownerPlace = some (q entry) := by
  rw [source_address]
  rfl
/-- Conditional on owner acceptance of the translator patch. Original entry
adopts the complete actual f31 success reply; no world reset or header premise. -/
theorem success142 {E : Type} (base : Carrier OWNER Data) (control : Control)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    {s : OWNER} {value : Foundation} (entry : Source7EntryOwned s value)
    (inner : Data) (post : OWNER) (events : List E)
    (reply : PV_STX2_Source7ReachedConstructor.handler base control fallback
      (PV_STX2_Source7ReachedReply.request entry) s = ⟨.returned (.ok inner),post,events⟩) :
    PV_STX2_SliceMachine.advance (PV_STX2_Source7ReachedConstructor.carrier base control fallback)
      control PV_STX2_SlicePrograms.dispatch
      (PV_STX2_Source7ReachedConstructor.handler base control fallback) 142
      ⟨.running (PV_STX2_Source7ReachedPointer.entryConfig entry),s,[]⟩ =
      ⟨.running (returned entry inner),post,events⟩ := by
  rw [PV_STX2_Source7ReachedReply.received142,reply]
  have counter := (PV_STX2_Source7ReachedLength.operands entry PV_STX2_Source7GlobalClone.value).2.1
  simp only [PV_STX2_Source7ConstructorReplies.received,returned,
    PV_STX2_Source7ReachedConstructor.config141,PV_STX2_SliceToVecEntry.called,counter]
/-- Conditional on owner acceptance of the translator patch. Actual original
result-binding configuration after the six generated aggregate/lifetime nodes. -/
def bound {s : OWNER} {value : Foundation} (entry : Source7EntryOwned s value) (inner : Data) : Config :=
  ⟨{activation := 15,remaining := PV_STX2_SliceF21.program.body.drop 16},
    (returned entry inner).callers,
    PV_STX2_SliceToVecConstruct.constructed (returned entry inner).store 15 inner⟩
/-- Conditional on owner acceptance of the translator patch. Execute the
source result binding from the actual original success continuation. The
existing generic six-instruction law is consumed by name, not re-proved. -/
theorem bound6 {E : Type} (base : Carrier OWNER Data) (control : Control)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    {s : OWNER} {value : Foundation} (entry : Source7EntryOwned s value)
    (inner : Data) (post : OWNER) :
    PV_STX2_SliceMachine.advance (PV_STX2_Source7ReachedConstructor.carrier base control fallback)
      control PV_STX2_SlicePrograms.dispatch
      (PV_STX2_Source7ReachedConstructor.handler base control fallback) 6
      ⟨.running (returned entry inner),post,[]⟩ = ⟨.running (bound entry inner),post,[]⟩ := by
  have input : (returned entry inner).store.cells ⟨15,8,[]⟩ = some inner := write_same _ _ _
  exact PV_STX2_SliceToVecConstruct.source6
    (PV_STX2_Source7ReachedConstructor.staticBase base control fallback) control
    (PV_STX2_Source7ReachedConstructor.handler base control fallback)
    (returned entry inner).store (returned entry inner).callers post 15 inner input
/-- Conditional on owner acceptance of the translator patch. Original entry
reaches the generated LOCAL0 Vec binding on the actual full success branch,
retaining its exact native post-world and event prefix. -/
theorem success148 {E : Type} (base : Carrier OWNER Data) (control : Control)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    {s : OWNER} {value : Foundation} (entry : Source7EntryOwned s value)
    (inner : Data) (post : OWNER) (events : List E)
    (reply : PV_STX2_Source7ReachedConstructor.handler base control fallback
      (PV_STX2_Source7ReachedReply.request entry) s = ⟨.returned (.ok inner),post,events⟩) :
    PV_STX2_SliceMachine.advance (PV_STX2_Source7ReachedConstructor.carrier base control fallback)
      control PV_STX2_SlicePrograms.dispatch
      (PV_STX2_Source7ReachedConstructor.handler base control fallback) 148
      ⟨.running (PV_STX2_Source7ReachedPointer.entryConfig entry),s,[]⟩ =
      ⟨.running (bound entry inner),post,events⟩ := by
  rw [PV_STX2_SliceDriverBuiltin.advance_add _ _ _ _ 142 6,
    success142 base control fallback entry inner post events reply]
  have execution := bound6 base control fallback entry inner post
  have framed := congrArg (PV_STX2_SlicePrefixEvents.prepend events) execution
  rw [← PV_STX2_SlicePrefixEvents.advance_prepend] at framed
  simpa only [PV_STX2_SlicePrefixEvents.prepend,List.append_nil] using framed
/-- Conditional on owner acceptance of the translator patch. The actual
result-local cell holds the exact source Vec aggregate containing the f31 reply. -/
theorem result_cell {s : OWNER} {value : Foundation} (entry : Source7EntryOwned s value) (inner : Data) :
    (bound entry inner).store.cells ⟨15,0,[]⟩ = some (PV_STX2_SliceToVecConstruct.vector inner) :=
  (PV_STX2_SliceToVecConstruct.cells (returned entry inner).store 15 inner).1
#print axioms success148
#print axioms result_cell
#print axioms bound
#print axioms bound6
#print axioms returned
#print axioms q
#print axioms resolved_q
#print axioms success142
#print axioms destination
#print axioms kind
#print axioms address
#print axioms ownerPlace
#print axioms source_address
end PV_STX2_Source7QBinding
