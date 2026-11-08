import PV_LIB_A_F6Prefix11
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F6Counter11
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_A_PrefixMachine11

/-- Same f6 entry carrier used by the provider; zero and boolean literals are
source semantics, not chosen native reply values. -/
def carrier (C : Carrier OWNER Data) (b : Bool) :=
  PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier C)) b

theorem call_quiet (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 16},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc; cases hc; rfl
  · intro c hc; cases hc; exact ⟨rfl,rfl,True.intro⟩

theorem wait_quiet (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running (PV_THR2_ScopeCall121.pending s a parents),w,es⟩,stack⟩ := by
  constructor
  · intro c hc; cases hc
    unfold PV_LIB_StoreActionTable.sourceSelect
    change (match P PV_THR2_ScopeCall121.fn with
      | some _ => none
      | none => (PV_LIB_StoreActionTable.v2Source PV_THR2_ScopeCall121.fn).bind _) = none
    cases P PV_THR2_ScopeCall121.fn <;> rfl
  · intro c hc; cases hc; exact ⟨rfl,rfl,True.intro⟩

/-- Actual1782 issuance; no new source simulation or chosen child activation. -/
theorem issue (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_LIB_StoreActionTable.Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    advance (carrier C b) K P resources encode H values 1
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 16},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨.running (PV_THR2_ScopeCall121.pending s a parents),w,es⟩,stack⟩,none⟩ := by
  rw [run _ K P resources encode H values 1 _ ⟨call_quiet P s a parents w es stack,True.intro⟩]
  simp only [PV_THR2_IntrinsicState.advance]
  rw [PV_THR2_IntrinsicCompatible.step _ K P H _ w es stack (by rfl)]
  dsimp only [carrier]
  rw [PV_THR2_ScopeCall121.issue C K P H s a parents b w]
  simp only [List.append_nil]

/-- FULL121 delivery at its actual source counter-constructor request.
The source table does not reinterpret this constructor as a source write. -/
theorem poll (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_LIB_StoreActionTable.Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    advance C K (PV_THR2_ScopeChildren.table P) resources encode H values 1
      ⟨⟨⟨.running (PV_THR2_ScopeCall121.pending s a parents),w,es⟩,stack⟩,none⟩ =
      ⟨PV_THR2_IntrinsicFullLocal.received C s a parents (PV_THR2_F6.live.body.drop 17)
        PV_THR2_ScopeCall121.fn [.number 0] 5 (PV_THR2_ScopeReply121.reply H s w) es stack,none⟩ := by
  rw [run C K _ resources encode H values 1 _ ⟨wait_quiet _ s a parents w es stack,True.intro⟩]
  exact congrArg (fun q => (⟨q,none⟩ : PV_LIB_StoreActionTable.SourceState))
    (PV_THR2_IntrinsicFullLocal.run C K _ H s a parents (PV_THR2_F6.live.body.drop 17)
      PV_THR2_ScopeCall121.fn [.number 0] 5 w es stack (by rfl) (PV_THR2_ScopeChildren.children P).1)

/-- Continuous corrected f6 entry history through its first constructor's FULL
reply; no returned-case, pointer, local read or numbering premise. It does not
claim the later Arc/callback/f15 history or the f6 complete delivery contract. -/
theorem history18 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_LIB_StoreActionTable.Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    advance (carrier C b) K (PV_THR2_ScopeChildren.table P) resources encode H values (16+(1+1))
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      ⟨PV_THR2_IntrinsicFullLocal.received (carrier C b) (PV_THR2_ScopePrologue.prepared s a)
        a parents (PV_THR2_F6.live.body.drop 17) PV_THR2_ScopeCall121.fn [.number 0] 5
        (PV_THR2_ScopeReply121.reply H (PV_THR2_ScopePrologue.prepared s a) w) es stack,none⟩ := by
  have start := PV_LIB_A_F6Prefix11.prologue_run
    (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier C)) K
    (PV_THR2_ScopeChildren.table P) resources encode H values s a parents b w es stack
  change advance (carrier C b) K _ resources encode H values 16 _ = _ at start
  rw [advance_add,start,advance_add,issue,poll]

#print axioms call_quiet
#print axioms wait_quiet
#print axioms issue
#print axioms poll
#print axioms history18
end PV_LIB_A_F6Counter11
