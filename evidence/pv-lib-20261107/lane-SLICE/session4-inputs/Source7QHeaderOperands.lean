import PV_STX2_Source7QAllocatedPointer
set_option autoImplicit false
namespace PV_STX2_Source7QHeaderOperands
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine
/-- Conditional on owner acceptance of the translator patch. Source phantom tag. -/
def phantomKind : Data := match PV_STX2_Source7CtorF35.node133 with
  | .leaf (.aggregateMove _ _ k _) => k
  | _ => .null
/-- Conditional on owner acceptance of the translator patch. Source pointer wrapper tag. -/
def pointerKind : Data := match PV_STX2_Source7CtorF35.node134 with
  | .leaf (.aggregateMove _ _ k _) => k
  | _ => .null
/-- Conditional on owner acceptance of the translator patch. Source pointer wrapper. -/
def pointerValue (pointer : Nat) : Data :=
  PV_STX2_Aggregates.pack pointerKind
    [.number pointer,PV_STX2_Aggregates.pack phantomKind []]
/-- Conditional on owner acceptance of the translator patch. Ordered source stores before s1417. -/
def stored (s : Store Data) (a pointer cap : Nat) (alloc : Data) : Store Data :=
  let s := write (write s ⟨a,49,[]⟩ none) ⟨a,49,[]⟩ (some (PV_STX2_Aggregates.pack phantomKind []))
  let s := write (write s ⟨a,49,[]⟩ none) ⟨a,17,[]⟩ (some (pointerValue pointer))
  let s := write (write s ⟨a,18,[]⟩ none) ⟨a,19,[]⟩ none
  let s := write (write s ⟨a,19,[]⟩ (some (.number cap))) ⟨a,20,[]⟩ none
  write (write s ⟨a,3,[]⟩ none) ⟨a,20,[]⟩ (some alloc)
/-- Conditional on owner acceptance of the translator patch. Required by
QHeaderStep.allocated_step: derive its pointer, capacity and allocator operands
by executing f35 nodes132..139, with the actual move out of allocator LOCAL3. -/
theorem source8 {W E : Type} (base : Carrier W Data) (ctrl : Control)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (parents : List Frame) (after : List PV_STX2_SliceSyntax.Node)
    (a pointer cap : Nat) (alloc : Data) (w : W)
    (p : s.cells ⟨a,18,[]⟩ = some (.number pointer))
    (n : s.cells ⟨a,1,[]⟩ = some (.number cap))
    (al : s.cells ⟨a,3,[]⟩ = some alloc) :
    advance (PV_STX2_Source7QRuntimeValues.carrier base) ctrl (fun _ => none) handler 8
      ⟨.running ⟨{activation := a,remaining := PV_STX2_Source7CtorF35.block166.drop 11 ++ after},parents,s⟩,w,[]⟩ =
      ⟨.running ⟨{activation := a,remaining := PV_STX2_Source7CtorF35.block166.drop 19 ++ after},
        parents,stored s a pointer cap alloc⟩,w,[]⟩ := by
  simp [PV_STX2_SliceMachine.advance,PV_STX2_SliceMachine.step,PV_STX2_Source7CtorF35.block166,
    PV_STX2_Source7CtorF35.node132,PV_STX2_Source7CtorF35.node133,
    PV_STX2_Source7CtorF35.node134,PV_STX2_Source7CtorF35.node135,
    PV_STX2_Source7CtorF35.node136,PV_STX2_Source7CtorF35.node137,
    PV_STX2_Source7CtorF35.node138,PV_STX2_Source7CtorF35.node139,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,
    PV_STX2_Source7QRuntimeValues.carrier,PV_STX2_Source7QRuntimeValues.arity,
    PV_STX2_Source7QRuntimeValues.scalarCast,PV_STX2_Aggregates.pack,
    stored,pointerValue,pointerKind,phantomKind,p,n,al]
#print axioms phantomKind
#print axioms pointerKind
#print axioms pointerValue
#print axioms stored
#print axioms source8
end PV_STX2_Source7QHeaderOperands
