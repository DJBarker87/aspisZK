import PV_STX2_SliceCloneNativeReads
set_option autoImplicit false
noncomputable section
namespace PV_STX2_SliceClonePointers
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceSyntax PV_STX2_SliceMachine

/- BEGIN GENERATED SELECTORS -/
/-- Conditional on owner acceptance of the translator patch. Exact source
payload pattern from N94906, generated without Data equality assumptions. -/
def isTransmute : Data → Bool
  | .object [("Cast", (.object [("Transmute", (.array [(.object [("Deduplicated", (.number 2205))]), (.object [("Deduplicated", (.number 2147))])]))]))] => true
  | _ => false
/-- Conditional on owner acceptance of the translator patch. Exact source
payload pattern from N94906, generated without Data equality assumptions. -/
def isPtrFromParts : Data → Bool
  | .object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Builtin", (.object [("PtrFromParts", (.atom "Shared"))]))]))])), ("generics", (.object [("regions", (.array [(.atom "Erased")])), ("types", (.array [(.object [("Deduplicated", (.number 2141))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))] => true
  | _ => false
/- END GENERATED SELECTORS -/

/-- Conditional on owner acceptance of the translator patch. The exact source
NonNull transmute preserves its native logical address. Other operators and
unrecognized native representations retain the base interpretation. This
installs no successful native parent lookup or physical address law. -/
def pointers {W : Type} (base : Carrier W Data) : Carrier W Data :=
  {base with unary := fun op value =>
    if isTransmute op then
      match PV_STX2_TypedReferences.decode value with
      | some (address,_) => some (PV_STX2_TypedReferences.reference address .null)
      | none => base.unary op value
    else base.unary op value}

/-- Conditional on owner acceptance of the translator patch. Install the
pointer interpretation beneath the SAME complete carrier from original entry;
previous prefix laws remain applicable by named base specialization. -/
def carrier {W : Type} (base : Carrier W Data) : Carrier W Data :=
  PV_STX2_SliceOutputEntry.carrier (pointers base)

/-- Conditional on owner acceptance of the translator patch. This exact
compiler builtin constructs a wide pointer from its actual pointer/metadata
operands. All unrelated or malformed requests retain the complete base reply,
including every native post-world/event/failure/pending answer. -/
def handler {W E : Type} (base : PV_STX2_Native.Request Data → W → Reply W E Data)
    (request : PV_STX2_Native.Request Data) (world : W) : Reply W E Data :=
  match request with
  | .child callee _ [pointer,metadata] =>
      if isPtrFromParts callee then
        match PV_STX2_TypedReferences.decode pointer with
        | some (address,_) =>
            ⟨.returned (.ok (PV_STX2_TypedReferences.reference address metadata)),world,[]⟩
        | none => base request world
      else base request world
  | _ => base request world

/-- Conditional on owner acceptance of the translator patch. The selected
cast is taken from the actual f13 node11, not a former cohort's type IDs. -/
def cast : Data := match PV_STX2_SliceF13.node11 with
  | .leaf (.bind _ _ (.unary op _)) => op
  | _ => .null
/-- Conditional on owner acceptance of the translator patch. The selected
PtrFromParts request is the actual f13 node15 including its mutability/type. -/
def callee : Data := match PV_STX2_SliceF13.node15 with
  | .leaf (.call _ f _ _ _) => f
  | _ => .null

/-- Conditional on owner acceptance of the translator patch. Transparent
NonNull-to-raw cast retains the same address under the complete carrier. The
native representation and actual parent descriptor still need association. -/
theorem cast_value {W : Type} (base : Carrier W Data) (p : Address) (metadata : Data) :
    (carrier base).unary cast (PV_STX2_TypedReferences.reference p metadata) =
      some (PV_STX2_TypedReferences.reference p .null) := by
  change (pointers base).unary cast (PV_STX2_TypedReferences.reference p metadata) = _
  simp [pointers,cast,PV_STX2_SliceF13.node11,isTransmute,PV_STX2_TypedReferences.roundtrip]

/-- Conditional on owner acceptance of the translator patch. PtrFromParts
keeps the exact source-supplied metadata and address with no allocation. -/
theorem parts_reply {W E : Type}
    (base : PV_STX2_Native.Request Data → W → Reply W E Data)
    (p : Address) (oldMetadata metadata : Data) (a : Nat) (w : W) :
    handler base (.child callee a [PV_STX2_TypedReferences.reference p oldMetadata,metadata]) w =
      ⟨.returned (.ok (PV_STX2_TypedReferences.reference p metadata)),w,[]⟩ := by
  simp [handler,callee,PV_STX2_SliceF13.node15,isPtrFromParts,PV_STX2_TypedReferences.roundtrip]

/-- Conditional on owner acceptance of the translator patch. One actual f13
node11 executes the selected native address-preserving transmute. The input
is a LOCAL cut operand, not a claimed reached parent/OWNER association. -/
theorem cast_step {W E : Type} (base : Carrier W Data) (control : Control)
    (nativeHandler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (parents : List Frame) (w : W) (a : Nat) (p : Address) (metadata : Data)
    (input : s.cells ⟨a,8,[]⟩ = some (PV_STX2_TypedReferences.reference p metadata)) :
    advance (carrier base) control PV_STX2_SlicePrograms.dispatch nativeHandler 1
      ⟨.running ⟨{activation := a,remaining := PV_STX2_SliceF13.program.body.drop 11},parents,s⟩,w,[]⟩ =
      ⟨.running ⟨{activation := a,remaining := PV_STX2_SliceF13.program.body.drop 12},
        parents,write s ⟨a,6,[]⟩ (some (PV_STX2_TypedReferences.reference p .null))⟩,w,[]⟩ := by
  have casted := cast_value base p metadata
  simp only [cast,PV_STX2_SliceF13.node11] at casted
  simp [PV_STX2_SliceMachine.advance,PV_STX2_SliceMachine.step,
    PV_STX2_SliceF13.program,PV_STX2_SliceF13.block25,PV_STX2_SliceF13.node11,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operand,
    PV_STX2_Store.read,input,casted,locate,writeAddress]

#print axioms isTransmute
#print axioms isPtrFromParts
#print axioms pointers
#print axioms carrier
#print axioms handler
#print axioms cast
#print axioms callee
#print axioms cast_value
#print axioms parts_reply
#print axioms cast_step
end PV_STX2_SliceClonePointers
