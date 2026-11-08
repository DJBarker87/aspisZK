import PV_LIB_A_F6Thread11
import PV_THR2_ScopeReply123
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F6Panic11
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_A_PrefixMachine11

/-- Same f6 entry carrier used by the provider; source literals are
source semantics, not chosen native reply values. -/
def carrier (C : Carrier OWNER Data) (b : Bool) :=
  PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier C)) b

theorem call_quiet (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 20},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc; cases hc; rfl
  · intro c hc; cases hc; exact ⟨rfl,rfl,True.intro⟩

theorem wait_quiet (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running (PV_THR2_ScopeCall123.pending s a parents),w,es⟩,stack⟩ := by
  constructor
  · intro c hc; cases hc
    unfold PV_LIB_StoreActionTable.sourceSelect
    change (match P PV_THR2_ScopeCall123.fn with
      | some _ => none
      | none => (PV_LIB_StoreActionTable.v2Source PV_THR2_ScopeCall123.fn).bind _) = none
    cases P PV_THR2_ScopeCall123.fn <;> rfl
  · intro c hc; cases hc; exact ⟨rfl,rfl,True.intro⟩

/-- Actual1875 issuance; no new source simulation or chosen child activation. -/
theorem issue (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_LIB_StoreActionTable.Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    advance (carrier C b) K P resources encode H values 1
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 20},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨.running (PV_THR2_ScopeCall123.pending s a parents),w,es⟩,stack⟩,none⟩ := by
  rw [run _ K P resources encode H values 1 _ ⟨call_quiet P s a parents w es stack,True.intro⟩]
  simp only [PV_THR2_IntrinsicState.advance]
  rw [PV_THR2_IntrinsicCompatible.step _ K P H _ w es stack (by rfl)]
  dsimp only [carrier]
  rw [PV_THR2_ScopeCall123.issue C K P H s a parents b w]
  simp only [List.append_nil]

/-- FULL123 delivery at its actual source panic-flag constructor request.
The source table does not reinterpret this constructor as a source write. -/
theorem poll (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_LIB_StoreActionTable.Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    advance C K (PV_THR2_ScopeChildren.table P) resources encode H values 1
      ⟨⟨⟨.running (PV_THR2_ScopeCall123.pending s a parents),w,es⟩,stack⟩,none⟩ =
      ⟨PV_THR2_IntrinsicFullLocal.received C s a parents (PV_THR2_F6.live.body.drop 21)
        PV_THR2_ScopeCall123.fn [.boolean false] 7 (PV_THR2_ScopeReply123.reply H s w) es stack,none⟩ := by
  rw [run C K _ resources encode H values 1 _ ⟨wait_quiet _ s a parents w es stack,True.intro⟩]
  exact congrArg (fun q => (⟨q,none⟩ : PV_LIB_StoreActionTable.SourceState))
    (PV_THR2_IntrinsicFullLocal.run C K _ H s a parents (PV_THR2_F6.live.body.drop 21)
      PV_THR2_ScopeCall123.fn [.boolean false] 7 w es stack (by rfl) (PV_THR2_ScopeChildren.children P).2.2.1)


/-- Source1821 storage before the actual panic-flag request. -/
theorem storage (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_LIB_StoreActionTable.Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    advance C K P resources encode H values 1
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 19},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 20},parents,
        write s ⟨a,7,[]⟩ none⟩,w,es⟩,stack⟩,none⟩ := by
  have quiet := PV_LIB_A_ChainTrace11.storage_quiet P s a parents []
    (PV_THR2_F6.live.body.drop 20)
    ⟨6,1821,.array [.atom "body",.atom "statements",.number 19]⟩ true 7 w es stack (by decide)
  change Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 19},parents,s⟩,w,es⟩,stack⟩ at quiet
  rw [run C K P resources encode H values 1 _ ⟨quiet,True.intro⟩]
  exact congrArg (fun q => (⟨q,none⟩ : PV_LIB_StoreActionTable.SourceState))
    (PV_THR2_IntrinsicFrameSteps.storage C K P H s a parents [] (PV_THR2_F6.live.body.drop 20)
      ⟨6,1821,.array [.atom "body",.atom "statements",.number 19]⟩ true 7 w es stack)

/-- Retain every123 reply from its actual preceding source continuation. -/
theorem segment3 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_LIB_StoreActionTable.Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    advance (carrier C b) K (PV_THR2_ScopeChildren.table P) resources encode H values (1+(1+1))
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 19},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      ⟨PV_THR2_IntrinsicFullLocal.received (carrier C b) (write s ⟨a,7,[]⟩ none)
        a parents (PV_THR2_F6.live.body.drop 21) PV_THR2_ScopeCall123.fn [.boolean false] 7
        (PV_THR2_ScopeReply123.reply H (write s ⟨a,7,[]⟩ none) w) es stack,none⟩ := by
  rw [advance_add,storage,advance_add,issue,poll]

#print axioms call_quiet
#print axioms wait_quiet
#print axioms issue
#print axioms poll
#print axioms storage
#print axioms segment3
end PV_LIB_A_F6Panic11
