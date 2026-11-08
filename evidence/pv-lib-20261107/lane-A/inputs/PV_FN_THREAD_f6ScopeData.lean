import PV_FN_THREAD_f6ConstructorRun
import PV_THR2_ScopeData
import PV_THR2_ScopeArcCall
import PV_THR2_PacketStructuredOneArg
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6ScopeData
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f6ConstructorRun

/-- The store at the ScopeData aggregate retains all three arbitrary payloads.
The only condition is the activation-counter clause of call-entry validity;
no read at this later source location is a premise. -/
theorem cells (s : Store Data) (a : Nat) (counter thread panicked : Data)
    (live : a < s.nextActivation) :
    let t := third (second (first s a counter) a thread) a panicked
    t.cells ⟨a,5,[]⟩ = some counter ∧ t.cells ⟨a,6,[]⟩ = some thread ∧
      t.cells ⟨a,7,[]⟩ = some panicked := by
  have neq (k i j : Nat) : (⟨a,i,[]⟩ : Address) ≠ ⟨s.nextActivation+k,j,[]⟩ := by
    intro eq
    exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le live (Nat.le_add_right _ _)))
      (congrArg Address.activation eq)
  have neq0 (i j : Nat) : (⟨a,i,[]⟩ : Address) ≠ ⟨s.nextActivation,j,[]⟩ := by
    exact neq 0 i j
  simp [first,second,third,PV_THR2_ScopePrologue.prepared,
    PV_THR2_StaticReply.returnedStore,PV_THR2_StaticCall.issued,
    PV_STX2_Native.arguments,write,neq,neq0,Nat.add_assoc]

/-- Three actual native calls allocate exactly three fresh activations. -/
theorem counter (s : Store Data) (a : Nat) (x y z : Data) :
    (third (second (first s a x) a y) a z).nextActivation = s.nextActivation + 3 := rfl

/-- Explicit source aggregation/lifetime stores and the saved1916 request.
This is the actual ScopeData instantiation of124, with the original lower
caller suffix; it does not claim that W2's Packet-only proof covers it. -/
def pending (s : Store Data) (a : Nat) (parents : List Frame) (x y z : Data) : Config :=
  let t := third (second (first s a x) a y) a z
  PV_THR2_ScopeArcCall.pending (PV_THR2_ScopeData.prepared t a x y z) a parents
    (PV_THR2_ScopeData.value x y z)

/-- The ScopeData payload is installed in124's actual argument1 by the
source move. No fixed reply or supplied receiver/pointee is used. -/
theorem argument (s : Store Data) (a : Nat) (parents : List Frame) (x y z : Data) :
    let c := pending s a parents x y z
    c.store.cells ⟨s.nextActivation+3,1,[]⟩ = some (PV_THR2_ScopeData.value x y z) ∧
      c.store.nextActivation = s.nextActivation+4 := by
  simp [pending,PV_THR2_ScopeArcCall.pending,PV_THR2_ScopeArcCall.before,
    PV_THR2_ScopeData.prepared,PV_THR2_StaticCall.pending,PV_THR2_StaticCall.issued,
    PV_STX2_Native.arguments,third,second,first,PV_THR2_ScopePrologue.prepared,
    PV_THR2_StaticReply.returnedStore,write,Nat.add_assoc]

#print axioms cells
#print axioms counter
#print axioms argument
end PV_FN_THREAD_f6ScopeData
