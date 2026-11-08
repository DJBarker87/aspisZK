import PV_LIB_A_Continue13
import PV_LIB_A_SequenceFrontier13
import PV_LIB_A_RangeInvariant12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_LoopBackedge13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11 PV_LIB_A_SourceSequence13
open PV_LIB_A_SequenceFrontier13

/-- Only source storage administration AFTER the handles push has delivered.
No handles push, destructor or other post-target callee is executed here. -/
def seq : Seq :=
  prepend PV_THR2_F15.node39 (prepend PV_THR2_F15.node40 (prepend PV_THR2_F15.node41 (prepend PV_THR2_F15.node42 (prepend PV_THR2_F15.node43 (prepend PV_THR2_F15.node44 (prepend PV_THR2_F15.node45 (.done)))))))

theorem shape : nodes seq ++ [PV_THR2_F15.node46] = PV_THR2_F15.block47.drop 24 := rfl

theorem off : sites seq := by
  change (15 : Nat) ≠ 361 ∧ (15 : Nat) ≠ 361 ∧ (15 : Nat) ≠ 361 ∧ (15 : Nat) ≠ 361 ∧ (15 : Nat) ≠ 361 ∧ (15 : Nat) ≠ 361 ∧ (15 : Nat) ≠ 361 ∧ True
  decide

def stored (s : Store Data) (a : Nat) :=
  write (write (write (write (write (write (write s ⟨a,15,[]⟩ none) ⟨a,14,[]⟩ none)
    ⟨a,13,[]⟩ none) ⟨a,12,[]⟩ none) ⟨a,11,[]⟩ none) ⟨a,10,[]⟩ none) ⟨a,8,[]⟩ none

theorem cost (C : Carrier OWNER Data) (s : Store Data) (a : Nat) (w : OWNER) :
    PV_LIB_A_SourceSequence13.steps C a w seq s = 7 := rfl

theorem keeps_iterator (s : Store Data) (a start finish : Nat)
    (before : PV_LIB_A_RangeInvariant12.Iterator s a start finish) :
    PV_LIB_A_RangeInvariant12.Iterator (stored s a) a start finish := by
  simpa [PV_LIB_A_RangeInvariant12.Iterator,stored,write] using before

theorem continue_quiet (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := [PV_THR2_F15.node46],loops := PV_LIB_A_RangeMatch12.loops},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc; cases hc; rfl
  · intro c hc; cases hc; exact ⟨rfl,rfl,True.intro⟩

/-- Exact emitted3530 backedge preserves the SAME iterator, store, world,
events, callers and suspended frames. Input is the post3519 continuation;
reaching that input from a prior successful iteration is a separate obligation. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    PV_LIB_A_PrefixMachine11.advance C K P resources encode H values 8
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.block47.drop 24,loops := PV_LIB_A_RangeMatch12.loops},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨.running (PV_THR2_Source15LoopEnter.after (stored s a) a parents),w,es⟩,stack⟩,none⟩ := by
  have first := PV_LIB_A_SourceSequence13.run C K P resources encode H values seq s a parents
    PV_LIB_A_RangeMatch12.loops [PV_THR2_F15.node46] w es stack off
  rw [shape,cost] at first
  change PV_LIB_A_PrefixMachine11.advance C K P resources encode H values 7 _ =
    ⟨⟨⟨.running ⟨{activation := a,remaining := [PV_THR2_F15.node46],loops := PV_LIB_A_RangeMatch12.loops},parents,stored s a⟩,w,es⟩,stack⟩,none⟩ at first
  change PV_LIB_A_PrefixMachine11.advance C K P resources encode H values (7+1) _ = _
  rw [advance_add,first]
  simp only [PV_LIB_A_PrefixMachine11.advance]
  change PV_LIB_A_DeferredActions.step C K P resources encode H values _ = _
  exact PV_LIB_A_Continue13.run C K P resources encode H values (stored s a) a parents
    ⟨15,3530,.array [.atom "body",.atom "statements",.number 12,.atom "kind",.atom "Loop",.atom "statements",.number 31]⟩
    PV_THR2_F15.block47 [] (PV_THR2_F15.live.body.drop 13) [] w es stack

#print axioms shape
#print axioms off
#print axioms cost
#print axioms keeps_iterator
#print axioms continue_quiet
#print axioms run
end PV_LIB_A_LoopBackedge13
