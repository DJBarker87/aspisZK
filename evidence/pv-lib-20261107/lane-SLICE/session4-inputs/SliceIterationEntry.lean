import PV_STX2_SliceCompleteAggregates
set_option autoImplicit false
noncomputable section
namespace PV_STX2_SliceIterationEntry
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceSyntax PV_STX2_SliceMachine
open PV_STX2_SliceLoopCallback PV_STX2_SliceWrappedEntry
open PV_STX2_SliceColumnEntry PV_STX2_SliceColumnPointer PV_STX2_SliceColumnBorrow

/-- Conditional on owner acceptance of the translator patch. Arbitrary source
callback entry, using the existing operand-derived configuration. -/
def callback (s : Store Data) (parents : List Frame) (index : Nat) : Config :=
  callbackConfig (preparedStore s index) parents index
/-- Conditional on owner acceptance of the translator patch. Arbitrary column
entry after the actual wrapper body, preserving the suspended loop parents. -/
def columnEntry (s : Store Data) (parents : List Frame) (index : Nat) : Config :=
  let c := callback s parents index
  columnConfig (wrappedStore c.store c.frame.activation index) c.callers c.frame.activation index
/-- Conditional on owner acceptance of the translator patch. Callback arguments
and fresh activation follow from source preparation and both MOVE operands. -/
theorem callback_facts (s : Store Data) (parents : List Frame) (index : Nat) :
    (callback s parents index).frame.activation = s.nextActivation ∧
    (callback s parents index).store.nextActivation = s.nextActivation+1 ∧
    (callback s parents index).store.cells ⟨s.nextActivation,1,[]⟩ = some wrapperReference ∧
    (callback s parents index).store.cells ⟨s.nextActivation,2,[]⟩ = some (indexTuple index) := by
  simp [callback,callbackConfig,preparedStore,PV_STX2_Native.arguments,write]
/-- Conditional on owner acceptance of the translator patch. The shared wrapper
survives callback preparation; freshness is an invariant on the source counter. -/
theorem callback_root (s : Store Data) (parents : List Frame) (index : Nat)
    (fresh : 10 ≤ s.nextActivation)
    (root : s.cells ⟨9,2,[]⟩ = some (wrapper index)) :
    (callback s parents index).store.cells ⟨9,2,[]⟩ = some (wrapper index) := by
  have ne : 9 ≠ s.nextActivation := by omega
  simp [callback,callbackConfig,preparedStore,PV_STX2_Native.arguments,write,Address.mk.injEq,ne,root]
/-- Conditional on owner acceptance of the translator patch. The next source
call obtains its activation and both captures from the wrapper MOVE operands. -/
theorem column_facts (s : Store Data) (parents : List Frame) (index : Nat) :
    (columnEntry s parents index).frame.activation = s.nextActivation+1 ∧
    (columnEntry s parents index).store.nextActivation = s.nextActivation+2 ∧
    (columnEntry s parents index).store.cells ⟨s.nextActivation+1,1,[]⟩ = some columnReference ∧
    (columnEntry s parents index).store.cells ⟨s.nextActivation+1,2,[]⟩ = some (indexTuple index) := by
  simp [columnEntry,columnConfig,columnStore,wrappedStore,callback,callbackConfig,
    preparedStore,PV_STX2_Native.arguments,write,Nat.add_assoc]
/-- Conditional on owner acceptance of the translator patch. The two fresh
child activations cannot overwrite the driver's mutable wrapper. -/
theorem column_root (s : Store Data) (parents : List Frame) (index : Nat)
    (fresh : 10 ≤ s.nextActivation)
    (root : s.cells ⟨9,2,[]⟩ = some (wrapper index)) :
    (columnEntry s parents index).store.cells ⟨9,2,[]⟩ = some (wrapper index) := by
  have f := callback_facts s parents index
  have kept := callback_root s parents index fresh root
  have ne : 9 ≠ (callback s parents index).frame.activation := by rw [f.1]; omega
  have ne' : 9 ≠ (callback s parents index).store.nextActivation := by rw [f.2.1]; omega
  simpa [columnEntry,columnConfig,columnStore,wrappedStore,PV_STX2_Native.arguments,
    write,Address.mk.injEq,ne,ne'] using kept

#print axioms callback
#print axioms columnEntry
#print axioms callback_facts
#print axioms callback_root
#print axioms column_facts
#print axioms column_root
end PV_STX2_SliceIterationEntry
