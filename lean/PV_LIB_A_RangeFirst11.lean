import PV_LIB_A_RangeHistory11
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_RangeFirst11
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame PV_FN_W4_NativeFootprint
open PV_LIB_StoreActionTable

def config (s : Store Data) (a : Nat) (parents : List Frame) (value : Data) : Config :=
  PV_THR2_Source15Loop93Issue.pending (PV_LIB_A_RangeHistoryV2.iteratorStore s a value) a parents

def afterWrite (s : Store Data) (a : Nat) (parents : List Frame) (value : Data) : Config :=
  let c := config s a parents value
  {c with store := write c.store ⟨a,7,[]⟩ (some (PV_LIB_A_Range165.sourceRange 2 16))}

/-- Derived from actual165's named meaning and the source move3423. This
replaces the local-cell premise of RangePoll11 at the first actual3447 poll. -/
theorem cell (C : Carrier OWNER Data) (D : Effects) (H : Backend PV_RJ4IDB.NativeEvent)
    (semantics : PV_LIB_A_Range165.PV_THR2_LibrarySemantics_RangeIntoIter165 C D H)
    (s : Store Data) (a : Nat) (parents : List Frame) (stack : List Config)
    (w : OWNER) (value : Data)
    (returned : (PV_THR2_Source15RangeToLoop.reply
      (PV_THR2_OwnUniformResourceHandler.lift H) s w).answer = .returned (.ok value)) :
    (config s a parents value).store.cells ⟨a,7,[]⟩ =
      some (PV_LIB_A_Range165.sourceRange 1 16) := by
  have valueEq := PV_LIB_A_RangeHistoryV2.returned165 C D H semantics s a parents stack w value returned
  rw [← show PV_THR2_Source15RangeAggregate.value = PV_LIB_A_Range165.sourceRange 1 16 from rfl,
    ← valueEq]
  exact PV_LIB_A_RangeHistoryV2.poll_local7 s a parents value

/-- Continuous corrected history from source3400 through the first3447 poll.
Every93 answer (including pending/fault/abort/divergence) is delivered on the
SAME incremented store. No local-cell/decoder/write-definedness premise remains.
This still starts at3400, not at the original f6/OwnInit entry. -/
theorem history (C : Carrier OWNER Data) (D : Effects) (H : Backend PV_RJ4IDB.NativeEvent)
    (semantics : PV_LIB_A_Range165.PV_THR2_LibrarySemantics_RangeIntoIter165 C D H)
    (K : Control) (P : Data → Option PV_STX2_SliceSyntax.Program)
    (resources : Resources) (encode : Encode) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) (value : Data)
    (returned : (PV_THR2_Source15RangeToLoop.reply
      (PV_THR2_OwnUniformResourceHandler.lift H) s w).answer = .returned (.ok value)) :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
    let handler := PV_THR2_OwnUniformResourceHandler.lift H
    let first := PV_THR2_Source15RangeToLoop.reply handler s w
    let iterator := PV_LIB_A_RangeHistoryV2.iteratorStore s a value
    let site := PV_LIB_A_RangePoll11.site iterator a
    PV_LIB_A_PrefixMachine11.advance B K (PV_LIB_A_RangePoll11.programs P) resources encode handler values
      ((PV_THR2_Source15RangeToLoop.steps handler s w + 7) + 1)
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 5},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      sourceReceive B (afterWrite s a parents value) (es ++ first.events) stack site .done
        (handler site.waiting.request first.world) := by
  intro B handler first iterator site
  rw [PV_LIB_A_PrefixMachine11.advance_add,
    PV_LIB_A_RangeHistory11.poll C K P resources encode handler values s a parents b w es stack value returned]
  simp only [PV_LIB_A_PrefixMachine11.advance]
  change PV_LIB_A_DeferredActions.step B K (PV_LIB_A_RangePoll11.programs P) resources encode handler values _ = _
  exact PV_LIB_A_RangePoll11.poll C K P resources encode handler values iterator a parents b
    first.world (es ++ first.events) stack 1 16 (cell C D H semantics s a parents stack w value returned)

/-- Source and OWNER effects are the exact full reply effects, on every arm.
The source count is already2 even if the native answer is pending. -/
theorem written (s : Store Data) (a : Nat) (parents : List Frame) (value : Data) :
    (afterWrite s a parents value).store.cells ⟨a,7,[]⟩ =
      some (PV_LIB_A_Range165.sourceRange 2 16) := write_same _ _ _

#print axioms cell
#print axioms history
#print axioms written
end PV_LIB_A_RangeFirst11
