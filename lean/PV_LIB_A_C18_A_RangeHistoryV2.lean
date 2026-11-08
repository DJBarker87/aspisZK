import PV_LIB_A_C18_A_RangeWriter
import PV_THR2_Source15RangeToLoop
import PV_THR2_Source15Loop93Issue
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_RangeHistoryV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_W1_LeafBoundary PV_W1_OwnerNativeFrame
open PV_FN_W4_NativeFootprint

def issued165 (s : Store Data) (a : Nat) : Store Data :=
  write (PV_THR2_Source15To165.prepared s a) ⟨a,6,[]⟩ none

def entry165 (s : Store Data) (a : Nat) (parents : List Frame) (stack : List Config) : Entry :=
  ⟨issued165 s a,a,parents,[],PV_THR2_F15.live.body.drop 9,
    PV_THR2_Source15RangeChild.fn165,[PV_THR2_Source15RangeAggregate.value],5,stack⟩

/-- The existing named165 source law at its ACTUAL source token and arguments.
No range identity is assumed for the returned payload. -/
theorem returned165 {E : Type} (C : Carrier OWNER Data) (D : Effects) (H : Backend E)
    (semantics : PV_LIB_A_Range165.PV_THR2_LibrarySemantics_RangeIntoIter165 C D H)
    (s : Store Data) (a : Nat) (parents : List Frame) (stack : List Config) (w : OWNER)
    (value : Data)
    (returned : (PV_THR2_Source15RangeToLoop.reply
      (PV_THR2_OwnUniformResourceHandler.lift H) s w).answer = .returned (.ok value)) :
    value = PV_THR2_Source15RangeAggregate.value := by
  have facts := semantics (entry165 s a parents stack) w PV_THR2_Source15RangeAggregate.value rfl
  exact (facts.2 value returned).1

def iteratorStore (s : Store Data) (a : Nat) (value : Data) : Store Data :=
  PV_THR2_Source15IteratorMove.prepared
    (PV_THR2_StaticReply.returnedStore (issued165 s a) a
      [PV_THR2_Source15RangeAggregate.value] 5 value) a value

/-- The source move3423 establishes local7. No local7 cell/history premise. -/
theorem local7 (s : Store Data) (a : Nat) (value : Data) :
    (iteratorStore s a value).cells ⟨a,7,[]⟩ = some value :=
  write_same _ _ _

/-- The emitted loop-entry and six-instruction request prefix preserve local7.
Only their symbolic write shape is inspected; no folded recurrence/run reduction. -/
theorem poll_local7 (s : Store Data) (a : Nat) (parents : List Frame) (value : Data) :
    (PV_THR2_Source15Loop93Issue.pending (iteratorStore s a value) a parents).store.cells
      ⟨a,7,[]⟩ = some value := by
  simp [PV_THR2_Source15Loop93Issue.pending,PV_THR2_Source15Loop93Prefix.pending,
    PV_THR2_Source15Loop93Prefix.prepared,PV_THR2_Source15Loop93Issue.prepared,
    PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write,local7]

/-- The exact first93 action is now derived from the actual165 returned VALUE
law and the continuous source-cell construction, not assumed as a Values field.
It is the FIRST loop iteration only; later iterations need their own invariant.
The full corrected-machine transport of the predecessor prefix remains open. -/
theorem first93_write {E : Type} (C : Carrier OWNER Data) (D : Effects) (H : Backend E)
    (semantics : PV_LIB_A_Range165.PV_THR2_LibrarySemantics_RangeIntoIter165 C D H)
    (s : Store Data) (a : Nat) (parents : List Frame) (stack : List Config)
    (b : Bool) (w : OWNER) (value : Data)
    (returned : (PV_THR2_Source15RangeToLoop.reply
      (PV_THR2_OwnUniformResourceHandler.lift H) s w).answer = .returned (.ok value)) :
    let before := (PV_THR2_Source15Loop93Issue.pending (iteratorStore s a value) a parents).store
    PV_THR2_SourceStoreLibrary.PV_THR2_LibrarySemantics_RangeNext93
      (PV_THR2_OwnInitExactReturnedCases.carrier C b)
      [PV_THR2_Source15Loop93Issue.ref a] before w =
      some (write before ⟨a,7,[]⟩ (some (PV_LIB_A_Range165.sourceRange 2 16))) := by
  have valueEq := returned165 C D H semantics s a parents stack w value returned
  have rangeEq : PV_THR2_Source15RangeAggregate.value = PV_LIB_A_Range165.sourceRange 1 16 := rfl
  intro before
  have cell : before.cells ⟨a,7,[]⟩ = some (PV_LIB_A_Range165.sourceRange 1 16) := by
    rw [← rangeEq,← valueEq]
    exact poll_local7 s a parents value
  exact PV_LIB_A_RangeWriter.range93 C b before w a 1 16 .null cell

/-- Reuse the original provider's complete prefix, including every165 answer.
This is explicitly the ORIGINAL interpreter theorem, never claimed to be a
full D984 run. Neutral-prefix transport is the separate remaining obligation. -/
theorem original_prefix {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool) (w : OWNER)
    (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance (PV_THR2_OwnInitExactReturnedCases.carrier C b) K
      (PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve P)))
      H (PV_THR2_Source15RangeToLoop.steps H s w)
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 5},parents,s⟩,w,es⟩,stack⟩ =
      PV_THR2_Source15RangeToLoop.after C b H s a parents w es stack :=
  PV_THR2_Source15RangeToLoop.run C K P H s a parents b w es stack

#print axioms returned165
#print axioms local7
#print axioms poll_local7
#print axioms first93_write
#print axioms original_prefix
end PV_LIB_A_RangeHistoryV2
