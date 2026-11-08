import PV_LIB_A_Post93Prefix12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_RangeTo270History12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame PV_FN_W4_NativeFootprint
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

/-- Continuous3400 through270 entry: actual165 move,93 write/full reply, both
Option arms, captures, closure,166 and Builder269. Retained source phases stop
without reset. This starts AFTER handles and does not claim14756 or f6 entry. -/
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
    let t := (PV_LIB_A_RangeFirst11.afterWrite s a parents value).store
    let site := PV_LIB_A_RangePoll11.site iterator a
    let r := handler site.waiting.request first.world
    let q := PV_LIB_A_RangeReply12.after B K iterator t a parents (es ++ first.events) stack r
    advance B K (PV_LIB_A_SpawnEnter12.enter270Programs P) resources encode handler values
      (((PV_THR2_Source15RangeToLoop.steps handler s w + 7) + 1) +
        PV_LIB_A_RangeReply12.steps B K iterator t a parents r + PV_LIB_A_Post93Prefix12.steps B handler q)
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 5},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      PV_LIB_A_Post93Prefix12.after B handler q := by
  intro B handler first iterator t site r q
  have initial := PV_LIB_A_RangeHistory12.history C D H semantics K
    (PV_THR2_SourceSpawnTable.resolve (PV_THR2_Source270Table.resolve P))
    resources encode values s a parents b w es stack value returned
  change advance B K (PV_LIB_A_SpawnEnter12.enter270Programs P) resources encode handler values
    (((PV_THR2_Source15RangeToLoop.steps handler s w + 7) + 1) +
      PV_LIB_A_RangeReply12.steps B K iterator t a parents r)
    ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 5},parents,s⟩,w,es⟩,stack⟩,none⟩ = q at initial
  rw [advance_add,initial]
  exact PV_LIB_A_Post93Prefix12.run B K P resources encode handler values q

#print axioms history
end PV_LIB_A_RangeTo270History12
