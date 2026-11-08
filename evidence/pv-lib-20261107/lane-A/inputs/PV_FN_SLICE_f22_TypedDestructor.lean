import PV_FN_SLICE_f7_DropRuntime
import PV_THR2_IntrinsicFrameAggregate
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f22_TypedDestructor
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
def node0 : PV_STX2_SliceSyntax.Node := .leaf (.storage ⟨22, 670, .array [(.atom "body"), (.atom "statements"), (.number 0)]⟩ true 0)
def unitKind : Data := .object [("Adt", (.array [(.object [("id", (.atom "Tuple")), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]), (.null), (.null)]))]
def node1 : PV_STX2_SliceSyntax.Node := .leaf (.aggregateMove ⟨22, 671, .array [(.atom "body"), (.atom "statements"), (.number 1)]⟩ (.local 0) unitKind [])
def node2 : PV_STX2_SliceSyntax.Node := .leaf (.storage ⟨22, 672, .array [(.atom "body"), (.atom "statements"), (.number 2)]⟩ false 1)
def node3 : PV_STX2_SliceSyntax.Node := .leaf (.ret ⟨22, 673, .array [(.atom "body"), (.atom "statements"), (.number 3)]⟩ (.local 0))
def body : List PV_STX2_SliceSyntax.Node := [node0,node1,node2,node3]

/-- Exact store at f22's own completion, before return administration.
No dereference of LOCAL1 occurs in the typed body. -/
def finalStore (s : Store Data) (a : Nat) : Store Data :=
  write (write (write s ⟨a,0,[]⟩ none) ⟨a,0,[]⟩
    (some (PV_STX2_Aggregates.pack unitKind []))) ⟨a,1,[]⟩ none

def state {E : Type} (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List E) (stack : List Config) (n : Nat) :
    PV_THR2_IntrinsicState.State OWNER E :=
  ⟨⟨.running ⟨{activation := a,remaining := body.drop n},parents,s⟩,w,es⟩,stack⟩

/-- Execute the ACTUAL f22 body through its own completion. Native answers,
caller stack and capture payload are unrestricted; the body issues no request. -/
theorem run {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier C) K P H 3
      (state s a parents w es stack 0) =
      state (finalStore s a) a parents w es stack 3 := by
  let B := PV_FN_SLICE_ValueCarrier.carrier C
  let s1 := write s ⟨a,0,[]⟩ none
  let s2 := write s1 ⟨a,0,[]⟩ (some (PV_STX2_Aggregates.pack unitKind []))
  have h0 : PV_THR2_IntrinsicState.advance B K P H 1
      (state s a parents w es stack 0) = state s1 a parents w es stack 1 := by
    exact PV_THR2_IntrinsicFrameSteps.storage B K P H s a parents []
      (body.drop 1) _ true 0 w es stack
  have h1 : PV_THR2_IntrinsicState.advance B K P H 1
      (state s1 a parents w es stack 1) = state s2 a parents w es stack 2 := by
    change PV_THR2_IntrinsicState.advance B K P H 1
      ⟨⟨.running ⟨{activation := a,remaining := node1 :: body.drop 2},parents,s1⟩,w,es⟩,stack⟩ = _
    unfold node1
    rw [PV_THR2_IntrinsicFrameAggregate.run]
    have unit : B.aggregate unitKind [] = some (PV_STX2_Aggregates.pack unitKind []) := rfl
    simp [PV_THR2_IntrinsicFrameAggregate.after,PV_STX2_Store.bind,evaluate,
      operands,locate,writeAddress,unit,state,s2,body]
  have h2 : PV_THR2_IntrinsicState.advance B K P H 1
      (state s2 a parents w es stack 2) =
      state (finalStore s a) a parents w es stack 3 := by
    exact PV_THR2_IntrinsicFrameSteps.storage B K P H s2 a parents []
      (body.drop 3) _ false 1 w es stack
  rw [show 3=1+2 by omega,PV_THR2_IntrinsicComposition.advance_add,h0,
    show 2=1+1 by omega,PV_THR2_IntrinsicComposition.advance_add,h1,h2]

/-- Every cell outside f22's own activation is unchanged, including all
cells reachable from the closure's captured pointer. -/
theorem frame (s : Store Data) (a : Nat) (p : Address) (other : p.activation ≠ a) :
    (finalStore s a).cells p = s.cells p := by
  have h0 : p ≠ (⟨a,0,[]⟩ : Address) := fun h => other (congrArg Address.activation h)
  have h1 : p ≠ (⟨a,1,[]⟩ : Address) := fun h => other (congrArg Address.activation h)
  simp only [finalStore,write,if_neg h0,if_neg h1]

/-- Source-store projection of the destructor on pre-existing caller cells.
The fresh f22 activation's dead locals are deliberately not projected. -/
def sourceProjection (s : Store Data) (a : Nat) : Address → Option Data :=
  fun p => if p.activation = a then s.cells p else (finalStore s a).cells p

theorem sourceProjection_identity (s : Store Data) (a : Nat) :
    sourceProjection s a = s.cells := by
  funext p
  by_cases h : p.activation = a
  · simp only [sourceProjection,if_pos h]
  · simp only [sourceProjection,if_neg h,frame s a p h]

/-- W5's general projection instantiated with the write result DERIVED from
f22. Identity follows from the destructor execution/frame above, not a chosen
native delta or a claim that the general reachability footprint is empty. -/
theorem w5_projection_identity (x : PV_FN_SLICE_f7_Drop.Cut) (a : Nat) :
    PV_FN_SLICE_f7_Drop.effects x (sourceProjection x.s a) = x.s := by
  classical
  rw [sourceProjection_identity]
  unfold PV_FN_SLICE_f7_Drop.effects PV_W5_DropLeaf.finalStore PV_FN_SLICE_f7_Drop.entry
  simp only [ite_self]

#print axioms run
#print axioms frame
#print axioms sourceProjection_identity
#print axioms w5_projection_identity
end PV_FN_SLICE_f22_TypedDestructor
