import PV_LIB_A_WeakGuardRun10
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WeakGuardSource10
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_A_WeakGuardRun10

def waiting (types : List Data) (s : Store Data) (p : Address) : PV_STX2_Native.Waiting Data :=
  ⟨.child (call types).2.1 s.nextActivation [PV_STX2_TypedReferences.reference p .null],
   .child s.nextActivation (call types).2.2.2.1,(call types).2.2.2.2⟩

/-- The writes are precisely661's storage, unit, moved receiver and call-argument
writes in source order. No whole-store result is supplied by a child law. -/
def prepared (s : Store Data) (a : Nat) (p : Address) : Store Data :=
  let s0 := write s ⟨a,1,[]⟩ (some (PV_STX2_TypedReferences.reference p .null))
  let s1 := write s0 ⟨a,0,[]⟩ none
  let s2 := write s1 ⟨a,2,[]⟩ none
  let s3 := write s2 ⟨a,3,[]⟩ none
  let s4 := write s3 ⟨a,0,[]⟩ (some PV_LIB_A_DestructorValues10.unitValue)
  let s5 := write s4 ⟨a,2,[]⟩ (some (PV_STX2_TypedReferences.reference p .null))
  let s6 := write s5 ⟨a,2,[]⟩ none
  PV_STX2_Native.arguments s.nextActivation [PV_STX2_TypedReferences.reference p .null] 1
    {s6 with nextActivation := s.nextActivation+1}

def after (types : List Data) (s : Store Data) (a : Nat)
    (parents : List Frame) (p : Address) : Config :=
  ⟨{activation := a,remaining := (PV_LIB_A_TypedBody661.program types).body.drop 6,
    waiting := some (waiting types s p)},parents,prepared s a p⟩

theorem run (C : Carrier OWNER Data) (K : Control) (b : Bool)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (types : List Data) (s : Store Data) (a : Nat) (parents : List Frame)
    (p : Address) (w : OWNER) :
    issued C K b P H types s a parents p w = ⟨.running (after types s a parents p),w,[]⟩ := by
  simp [PV_LIB_A_GenericDropMachine.unitTag,after,prepared,waiting,issued,entry,PV_STX2_Native.arguments,PV_LIB_A_DestructorValues10.unitValue,PV_STX2_SliceMachine.advance,PV_STX2_SliceMachine.step,
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


/-- All old source roots remain, independently of T and Weak's payload.
Numbering at the caller discharges these two local inequalities. -/
theorem older_cell (s : Store Data) (a : Nat) (p q : Address)
    (parent : q.activation ≠ a) (child : q.activation ≠ s.nextActivation) :
    (prepared s a p).cells q = s.cells q := by
  have other (i : Nat) : q ≠ (⟨a,i,[]⟩ : Address) := by
    intro same
    exact parent (congrArg Address.activation same)
  have callee : q ≠ (⟨s.nextActivation,1,[]⟩ : Address) := by
    intro same
    exact child (congrArg Address.activation same)
  simp only [prepared,PV_STX2_Native.arguments,write,if_neg (other 0),
    if_neg (other 1),if_neg (other 2),if_neg (other 3),if_neg callee]

theorem next_activation (s : Store Data) (a : Nat) (p : Address) :
    (prepared s a p).nextActivation = s.nextActivation+1 := rfl

#print axioms waiting
#print axioms prepared
#print axioms after
#print axioms run
#print axioms older_cell
#print axioms next_activation
end PV_LIB_A_WeakGuardSource10
