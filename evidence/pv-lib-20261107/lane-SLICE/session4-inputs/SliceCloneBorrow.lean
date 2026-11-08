import PV_STX2_SliceCloneParts
set_option autoImplicit false
noncomputable section
namespace PV_STX2_SliceCloneBorrow
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceSyntax PV_STX2_SliceMachine PV_STX2_SliceClonePointers

/-- Conditional on owner acceptance of the translator patch. The installed
native slice pointer retains its exact address through dereference. -/
theorem dereference_value {W : Type} (base : Carrier W Data) (w : W)
    (p : Address) (metadata : Data) :
    (carrier base).dereference w (PV_STX2_TypedReferences.reference p metadata) = some p := by
  change (PV_STX2_TypedReferences.carrier
    (PV_STX2_SliceLoopGuard.comparisons (PV_STX2_SliceColumnPointer.one
      (PV_STX2_SliceOutputInterpretation.arrayWrites (pointers base))))).dereference w
    (PV_STX2_TypedReferences.reference p metadata) = _
  exact PV_STX2_TypedReferences.dereference _ w p metadata

/-- Conditional on owner acceptance of the translator patch. Native slice
metadata is the actual PtrFromParts operand, preserved during reborrow. -/
theorem metadata_value {W : Type} (base : Carrier W Data) (p : Address) (metadata : Data) :
    (carrier base).metadata (PV_STX2_TypedReferences.reference p metadata) = some metadata := by
  change (PV_STX2_TypedReferences.carrier
    (PV_STX2_SliceLoopGuard.comparisons (PV_STX2_SliceColumnPointer.one
      (PV_STX2_SliceOutputInterpretation.arrayWrites (pointers base))))).metadata
    (PV_STX2_TypedReferences.reference p metadata) = _
  exact PV_STX2_TypedReferences.metadata _ p metadata

/-- Conditional on owner acceptance of the translator patch. Reference
construction uses the same native address/metadata representation throughout. -/
theorem reference_value {W : Type} (base : Carrier W Data) (p : Address) (metadata : Data) :
    (carrier base).reference p metadata = PV_STX2_TypedReferences.reference p metadata := rfl

/-- Conditional on owner acceptance of the translator patch. Actual source
nodes16..19 clear the length/raw temporaries, reborrow the native wide pointer
into LOCAL4 and end LOCAL5. -/
def prepared (s : Store Data) (a : Nat) (p : Address) (metadata : Data) : Store Data :=
  write (write (write (write s ⟨a,7,[]⟩ none) ⟨a,6,[]⟩ none)
    ⟨a,4,[]⟩ (some (PV_STX2_TypedReferences.reference p metadata))) ⟨a,5,[]⟩ none

/-- Conditional on owner acceptance of the translator patch. Four actual
source transitions derive the f21 slice argument from the PtrFromParts return. -/
theorem source4 {W E : Type} (base : Carrier W Data) (control : Control)
    (nativeHandler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (parents : List Frame) (w : W) (a : Nat) (p : Address) (metadata : Data)
    (input : s.cells ⟨a,5,[]⟩ = some (PV_STX2_TypedReferences.reference p metadata)) :
    advance (carrier base) control PV_STX2_SlicePrograms.dispatch nativeHandler 4
      ⟨.running ⟨{activation := a,remaining := PV_STX2_SliceF13.program.body.drop 16},parents,s⟩,w,[]⟩ =
      ⟨.running ⟨{activation := a,remaining := PV_STX2_SliceF13.program.body.drop 20},
        parents,prepared s a p metadata⟩,w,[]⟩ := by
  simp [PV_STX2_SliceMachine.advance,PV_STX2_SliceMachine.step,
    PV_STX2_SliceF13.program,PV_STX2_SliceF13.block25,PV_STX2_SliceF13.node16,
    PV_STX2_SliceF13.node17,PV_STX2_SliceF13.node18,PV_STX2_SliceF13.node19,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operand,
    PV_STX2_Store.read,locate,writeAddress,write,input,dereference_value,
    metadata_value,reference_value,prepared]

/-- Conditional on owner acceptance of the translator patch. Both source
moves happen before f21 activation allocation, slice first then allocator. -/
def childStore (s : Store Data) (a : Nat) (slice alloc : Data) : Store Data :=
  PV_STX2_Native.arguments s.nextActivation [slice,alloc] 1
    {write (write s ⟨a,4,[]⟩ none) ⟨a,2,[]⟩ none with nextActivation := s.nextActivation+1}
/-- Conditional on owner acceptance of the translator patch. f21's actual
caller frame retains the emitted source cleanup, destination and all parents. -/
def childConfig (s : Store Data) (parents : List Frame) (a : Nat) (slice alloc : Data) : Config :=
  ⟨{activation := s.nextActivation,remaining := PV_STX2_SliceF21.program.body},
    PV_STX2_SliceEntries.F13S547.saved a s.nextActivation
      (PV_STX2_SliceF13.program.body.drop 21) [slice,alloc] :: parents,
    childStore s a slice alloc⟩

/-- Conditional on owner acceptance of the translator patch. Actual f13
node20 and dispatch derive f21's activation and both captures. The existing
source-call entry law is reused by name; no arbitrary f21 activation is supplied. -/
theorem source_entry2 {W E : Type} (base : Carrier W Data) (control : Control)
    (nativeHandler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (parents : List Frame) (w : W) (a : Nat) (slice alloc : Data)
    (sliceOperand : s.cells ⟨a,4,[]⟩ = some slice)
    (allocOperand : s.cells ⟨a,2,[]⟩ = some alloc) :
    advance (carrier base) control PV_STX2_SlicePrograms.dispatch nativeHandler 2
      ⟨.running ⟨{activation := a,remaining := PV_STX2_SliceF13.program.body.drop 20},parents,s⟩,w,[]⟩ =
      ⟨.running (childConfig s parents a slice alloc),w,[]⟩ := by
  change advance _ _ _ _ 2
    ⟨.running (PV_STX2_SliceEntries.F13S547.caller a
      (PV_STX2_SliceF13.program.body.drop 21) parents s),w,[]⟩ = _
  rw [PV_STX2_SliceEntries.F13S547.source_call_entry]
  simp [PV_STX2_SliceEntries.F13S547.captures,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,sliceOperand,allocOperand,
    childConfig,childStore]

#print axioms dereference_value
#print axioms metadata_value
#print axioms reference_value
#print axioms prepared
#print axioms source4
#print axioms childStore
#print axioms childConfig
#print axioms source_entry2
end PV_STX2_SliceCloneBorrow
