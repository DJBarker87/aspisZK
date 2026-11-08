import PV_LIB_A_DestructorValues10
import PV_LIB_A_TypedBody661
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WeakGuardRun10
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine

/-- The original source carrier; no allocator or destructor reply is installed. -/
def carrier (C : Carrier OWNER Data) (b : Bool) :=
  PV_LIB_A_DestructorValues10.carrier C b

/-- Begin actual glue661 with the source pointer issued by typed Drop entry.
The lower source stack is retained verbatim. -/
def entry (types : List Data) (s : Store Data) (a : Nat)
    (parents : List Frame) (p : Address) : Config :=
  ⟨{activation := a,remaining := (PV_LIB_A_TypedBody661.program types).body},parents,
    write s ⟨a,1,[]⟩ (some (PV_STX2_TypedReferences.reference p .null))⟩

/-- The call token and cleanup are read from the ACTUAL661 node, not rebuilt. -/
def call (types : List Data) : Site × Data × List Operand × PV_STX2_Syntax.Place × List Instruction :=
  match PV_LIB_A_TypedBody661.node5 types with
  | .leaf (.call site fn args dest cleanup) => (site,fn,args,dest,cleanup)
  | _ => (⟨0,0,.null⟩,.null,[],.local 0,[])

/-- Exact six-instruction prefix, ending when683 is ISSUED, before any reply. -/
def issued (C : Carrier OWNER Data) (K : Control) (b : Bool)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (types : List Data) (s : Store Data) (a : Nat) (parents : List Frame)
    (p : Address) (w : OWNER) :=
  PV_STX2_SliceMachine.advance (carrier C b) K P H 6
    ⟨.running (entry types s a parents p),w,[]⟩

/-- Prefix does not read the Weak payload or call its native handler. It issues
683 with the same source address and preserves all source roots outside661. -/
theorem issued_graph (C : Carrier OWNER Data) (K : Control) (b : Bool)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (types : List Data) (s : Store Data) (a : Nat) (parents : List Frame)
    (p : Address) (w : OWNER) :
    ∃ c wait,
      issued C K b P H types s a parents p w = ⟨.running c,w,[]⟩ ∧
      c.frame.waiting = some wait ∧
      wait.request = .child (call types).2.1 s.nextActivation
        [PV_STX2_TypedReferences.reference p .null] ∧
      c.callers = parents := by
  simp [issued,entry,PV_STX2_SliceMachine.advance,PV_STX2_SliceMachine.step,
    PV_STX2_SliceMachine.native,PV_STX2_SliceMachine.adopt,
    PV_LIB_A_TypedBody661.program,PV_LIB_A_TypedBody661.block11,
    PV_LIB_A_TypedBody661.node0,PV_LIB_A_TypedBody661.node1,
    PV_LIB_A_TypedBody661.node2,PV_LIB_A_TypedBody661.node3,
    PV_LIB_A_TypedBody661.node4,PV_LIB_A_TypedBody661.node5,
    PV_STX2_Native.step,PV_STX2_Store.bind,PV_STX2_Store.evaluate,
    PV_STX2_Store.operand,PV_STX2_Store.operands,PV_STX2_Store.read,
    PV_STX2_Store.locate,PV_STX2_Store.writeAddress,write,
    carrier,PV_LIB_A_DestructorValues10.carrier,
    PV_THR2_AggregateCompletion.carrier,PV_THR2_OwnInitExactReturnedCases.carrier,
    PV_THR2_EntryDynamic.carrier,PV_THR2_Scalars.carrier,
    PV_STX2_TypedReferences.carrier,PV_STX2_LengthBranch.carrier,
    PV_STX2_Aggregates.carrier,PV_STX2_Aggregates.aggregate,
    PV_THR2_FunctionValues.base,PV_THR2_KeyInstall.carrier,
    PV_THR2_KeyValues.carrier,PV_THR2_ThreadFields.carrier,
    PV_STX2_TypedReferences.roundtrip,call]

#print axioms carrier
#print axioms entry
#print axioms call
#print axioms issued
#print axioms issued_graph
end PV_LIB_A_WeakGuardRun10
