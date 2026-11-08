import PV_LIB_A_RangeTo270History12
import PV_LIB_A_RangeInvariant12
import PV_LIB_A_RangeTailTrace11
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_RangeIteration13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

/-- The actual six-step preparation at ANY iteration entry. The exact carrier
already used by the first iteration supplies the self-created source references. -/
theorem prepared (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
    PV_LIB_A_PrefixMachine11.advance B K P resources encode H values 6
      ⟨⟨⟨.running (PV_THR2_Source15LoopEnter.after s a parents),w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨.running (PV_THR2_Source15Loop93Issue.pending s a parents),w,es⟩,stack⟩,none⟩ := by
  intro B
  rw [PV_LIB_A_PrefixMachine11.run B K P resources encode H values _ _
    (PV_LIB_A_RangeTailTrace11.loop6 _ K P H s a parents b w es stack)]
  exact congrArg (fun q => (⟨q,none⟩ : SourceState))
    (PV_THR2_Source15Loop93Issue.run _ K P H s a parents b w es stack)

/-- One entire target-prefix iteration, from the live loop entry through270
entry on Some, loop exit on None, or the exact earlier stop. Input Iterator is
the induction facet, not a new row Pre; prior-callee preservation remains separate. -/
theorem history (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (start finish : Nat) (iterator : PV_LIB_A_RangeInvariant12.Iterator s a start finish) :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
    let t := PV_LIB_A_RangeInvariant12.post s a parents start finish
    let site := PV_LIB_A_RangePoll11.site s a
    let r := H site.waiting.request w
    let q := PV_LIB_A_RangeReply12.after B K s t a parents es stack r
    PV_LIB_A_PrefixMachine11.advance B K (PV_LIB_A_SpawnEnter12.enter270Programs P) resources encode H values
      ((6+1) + PV_LIB_A_RangeReply12.steps B K s t a parents r + PV_LIB_A_Post93Prefix12.steps B H q)
      ⟨⟨⟨.running (PV_THR2_Source15LoopEnter.after s a parents),w,es⟩,stack⟩,none⟩ =
      PV_LIB_A_Post93Prefix12.after B H q := by
  intro B t site r q
  let T := PV_LIB_A_SpawnEnter12.enter270Programs P
  rw [advance_add,advance_add,advance_add,prepared C K T resources encode H values s a parents b w es stack]
  simp only [PV_LIB_A_PrefixMachine11.advance]
  have poll := PV_LIB_A_RangeInvariant12.poll C K
    (PV_THR2_SourceSpawnTable.resolve (PV_THR2_Source270Table.resolve P)) resources encode H values
    s a parents b w es stack start finish iterator
  change PV_LIB_A_DeferredActions.step B K T resources encode H values _ = _ at poll
  rw [poll,PV_LIB_A_RangeReply12.run B K T resources encode H values s t a parents es stack r]
  exact PV_LIB_A_Post93Prefix12.run B K P resources encode H values q

#print axioms prepared
#print axioms history
end PV_LIB_A_RangeIteration13
