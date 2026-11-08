import PV_LIB_A_WeakGuardPrefix10
import PV_LIB_A_TypedBody584
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WeakGuardBuild10
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine

def kind (types : List Data) : Data :=
  match PV_LIB_A_TypedBody584.node7 types with
  | .leaf (.aggregateMove _ _ tag _) => tag
  | _ => .null

/-- Exactly the implicit Weak value constructed by actual584. It borrows the
source Arc's allocator field; it never copies or defaults that allocator. -/
def guard (types : List Data) (ptr : Data) (root slot : Nat) : Data :=
  PV_THR2_KeyValues.pack (kind types)
    [ptr,PV_STX2_TypedReferences.reference ⟨root,slot,[2]⟩ .null]

def entry (types : List Data) (s : Store Data) (a : Nat)
    (parents : List Frame) (root slot : Nat) : Config :=
  ⟨{activation := a,remaining := (PV_LIB_A_TypedBody584.program types).body},parents,
    write s ⟨a,1,[]⟩ (some (PV_STX2_TypedReferences.reference ⟨root,slot,[]⟩ .null))⟩

/-- Per-instruction stores avoid normalizing an eight-step unknown read tree. -/
def stage (types : List Data) (s : Store Data) (a root slot : Nat) (ptr : Data) : Nat → Store Data
  | 0 => (entry types s a [] root slot).store
  | 1 => write (stage types s a root slot ptr 0) ⟨a,0,[]⟩ none
  | 2 => write (stage types s a root slot ptr 1) ⟨a,0,[]⟩ (some PV_LIB_A_DestructorValues10.unitValue)
  | 3 => write (stage types s a root slot ptr 2) ⟨a,2,[]⟩ none
  | 4 => write (stage types s a root slot ptr 3) ⟨a,3,[]⟩ none
  | 5 => write (stage types s a root slot ptr 4) ⟨a,3,[]⟩ (some ptr)
  | 6 => write (stage types s a root slot ptr 5) ⟨a,4,[]⟩ none
  | 7 => write (stage types s a root slot ptr 6) ⟨a,4,[]⟩
      (some (PV_STX2_TypedReferences.reference ⟨root,slot,[2]⟩ .null))
  | n+8 => write (write (write (stage types s a root slot ptr 7) ⟨a,3,[]⟩ none)
      ⟨a,4,[]⟩ none) ⟨a,2,[]⟩ (some (guard types ptr root slot))

def configuration (types : List Data) (s : Store Data) (a : Nat) (parents : List Frame)
    (root slot : Nat) (ptr : Data) (n : Nat) : Config :=
  ⟨{activation := a,remaining := (PV_LIB_A_TypedBody584.program types).body.drop n},parents,
    stage types s a root slot ptr n⟩

/-- Actual584's source guard construction from the provider's exact Arc value.
The allocator is read at the real source field, never supplied as an extra fact. -/
theorem raw_step (C : Carrier OWNER Data) (K : Control) (b : Bool)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (types : List Data) (s : Store Data) (a : Nat) (parents : List Frame)
    (root slot : Nat) (ptr : Data) (w : OWNER)
    (older : root ≠ a)
    (source : s.cells ⟨root,slot,[]⟩ = some
      (PV_THR2_Packet315SourceReturn.value ptr PV_THR2_Packet218ReturnData.allocator))
    (n : Nat) (bound : n < 8) :
    PV_STX2_SliceMachine.step
      (PV_LIB_A_UnwindMatch.carrier (PV_LIB_A_DestructorValues10.carrier C b) K) K P H
      (configuration types s a parents root slot ptr n) w =
      ⟨.running (configuration types s a parents root slot ptr (n+1)),w,[]⟩ := by
  have different (i : Nat) : (⟨root,slot,[]⟩ : Address) ≠ ⟨a,i,[]⟩ := by
    intro same
    exact older (congrArg Address.activation same)
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [configuration,stage,PV_LIB_A_UnwindMatch.carrier,PV_LIB_A_DestructorValues10.unitValue,PV_LIB_A_GenericDropMachine.unitTag,entry,PV_STX2_SliceMachine.advance,PV_STX2_SliceMachine.step,
    PV_STX2_SliceMachine.native,PV_STX2_SliceMachine.adopt,
    PV_LIB_A_TypedBody584.program,PV_LIB_A_TypedBody584.block30,
    PV_LIB_A_TypedBody584.node0,PV_LIB_A_TypedBody584.node1,
    PV_LIB_A_TypedBody584.node2,PV_LIB_A_TypedBody584.node3,
    PV_LIB_A_TypedBody584.node4,PV_LIB_A_TypedBody584.node5,
    PV_LIB_A_TypedBody584.node6,PV_LIB_A_TypedBody584.node7,
    PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operand,operands,
    PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,write,
    PV_LIB_A_DestructorValues10.carrier,PV_THR2_AggregateCompletion.carrier,
    PV_THR2_OwnInitExactReturnedCases.carrier,PV_THR2_EntryDynamic.carrier,
    PV_THR2_Scalars.carrier,PV_STX2_TypedReferences.carrier,
    PV_STX2_LengthBranch.carrier,PV_STX2_Aggregates.carrier,
    PV_STX2_Aggregates.aggregate,PV_THR2_FunctionValues.base,
    PV_THR2_KeyInstall.carrier,PV_THR2_KeyValues.carrier,
    PV_THR2_ThreadFields.carrier,PV_STX2_TypedReferences.roundtrip,
    PV_THR2_Packet315SourceReturn.value,older,PV_THR2_KeyValues.pack,different,source,guard,kind]


#print axioms kind
#print axioms guard
#print axioms entry
#print axioms stage
#print axioms configuration
#print axioms raw_step
end PV_LIB_A_WeakGuardBuild10
