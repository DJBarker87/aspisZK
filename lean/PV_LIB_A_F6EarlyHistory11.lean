import PV_LIB_A_F6Panic11
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F6EarlyHistory11
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_A_PrefixMachine11
abbrev Event := PV_RJ4IDB.NativeEvent
abbrev Handler := PV_LIB_StoreActionTable.Handler

def threadStore (s : Store Data) (a : Nat) (counter : Data) : Store Data :=
  write (PV_THR2_StaticReply.returnedStore s a [.number 0] 5 counter) ⟨a,6,[]⟩ none

def panicStore (s : Store Data) (a : Nat) (counter thread : Data) : Store Data :=
  write (PV_THR2_StaticReply.returnedStore (threadStore s a counter) a [] 6 thread) ⟨a,7,[]⟩ none

/-- Exact branch-dependent fuel: failed/pending121 stays there; successful121
executes122; successful122 executes123. No native reply is fixed to success. -/
def steps (H : Handler) (s : Store Data) (a : Nat) (r : Reply OWNER Event Data) : Nat :=
  match r.answer with
  | .returned (.ok counter) =>
    3 + match (PV_THR2_ScopeReply122.reply H (threadStore s a counter) r.world).answer with
      | .returned (.ok _) => 3
      | _ => 0
  | _ => 0

def after (C : Carrier OWNER Data) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (r : Reply OWNER Event Data) (es : List Event) (stack : List Config) :
    PV_LIB_StoreActionTable.SourceState :=
  match r.answer with
  | .returned (.ok counter) =>
    let t := threadStore s a counter
    let r2 := PV_THR2_ScopeReply122.reply H t r.world
    match r2.answer with
    | .returned (.ok thread) =>
      let u := panicStore s a counter thread
      ⟨PV_THR2_IntrinsicFullLocal.received C u a parents (PV_THR2_F6.live.body.drop 21)
        PV_THR2_ScopeCall123.fn [.boolean false] 7 (PV_THR2_ScopeReply123.reply H u r2.world)
        ((es ++ r.events) ++ r2.events) stack,none⟩
    | _ => ⟨PV_THR2_IntrinsicFullLocal.received C t a parents (PV_THR2_F6.live.body.drop 19)
        PV_THR2_ScopeCall122.fn [] 6 r2 (es ++ r.events) stack,none⟩
  | _ => ⟨PV_THR2_IntrinsicFullLocal.received C s a parents (PV_THR2_F6.live.body.drop 17)
      PV_THR2_ScopeCall121.fn [.number 0] 5 r es stack,none⟩

/-- Same f6 source store and actual issued child activations throughout.
The branch split is in the conclusion, including every retained early stop. -/
theorem continuation (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER Event) (s : Store Data) (a : Nat)
    (parents : List Frame) (b : Bool) (r : Reply OWNER Event Data)
    (es : List Event) (stack : List Config) :
    let B := PV_LIB_A_F6Counter11.carrier C b
    advance B K (PV_THR2_ScopeChildren.table P) resources encode H values (steps H s a r)
      ⟨PV_THR2_IntrinsicFullLocal.received B s a parents (PV_THR2_F6.live.body.drop 17)
        PV_THR2_ScopeCall121.fn [.number 0] 5 r es stack,none⟩ =
      after B H s a parents r es stack := by
  intro B
  rcases r with ⟨answer,world,events⟩
  cases answer with
  | pending => rfl
  | fault f => rfl
  | returned result =>
    cases result with
    | fail e => rfl
    | div => rfl
    | ok counter =>
      simp only [steps,after]
      rw [advance_add,PV_THR2_IntrinsicFullLocal.returned]
      have next := PV_LIB_A_F6Thread11.segment3 C K P resources encode H values
        (PV_THR2_StaticReply.returnedStore s a [.number 0] 5 counter) a parents b world (es ++ events) stack
      change advance B K (PV_THR2_ScopeChildren.table P) resources encode H values 3 _ = _ at next
      rw [next]
      change advance B K (PV_THR2_ScopeChildren.table P) resources encode H values
        (match (PV_THR2_ScopeReply122.reply H (threadStore s a counter) world).answer with
          | .returned (.ok _) => 3 | _ => 0)
        ⟨PV_THR2_IntrinsicFullLocal.received B (threadStore s a counter) a parents
          (PV_THR2_F6.live.body.drop 19) PV_THR2_ScopeCall122.fn [] 6
          (PV_THR2_ScopeReply122.reply H (threadStore s a counter) world) (es ++ events) stack,none⟩ = _
      generalize hr : PV_THR2_ScopeReply122.reply H (threadStore s a counter) world = r2
      rcases r2 with ⟨answer2,world2,events2⟩
      cases answer2 with
      | pending => rfl
      | fault f => rfl
      | returned result2 =>
        cases result2 with
        | fail e => rfl
        | div => rfl
        | ok thread =>
          rw [PV_THR2_IntrinsicFullLocal.returned]
          exact PV_LIB_A_F6Panic11.segment3 C K P resources encode H values
            (PV_THR2_StaticReply.returnedStore (threadStore s a counter) a [] 6 thread)
            a parents b world2 ((es ++ events) ++ events2) stack

/-- Continuous corrected execution from f6 body entry through123 or the first
retained121/122 stop. This is an early prefix, not f6's complete Post and not
an original OwnInit-entry-to14756 history. -/
theorem history (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER Event) (s : Store Data) (a : Nat)
    (parents : List Frame) (b : Bool) (w : OWNER) (es : List Event) (stack : List Config) :
    let t := PV_THR2_ScopePrologue.prepared s a
    let r := PV_THR2_ScopeReply121.reply H t w
    let B := PV_LIB_A_F6Counter11.carrier C b
    advance B K (PV_THR2_ScopeChildren.table P) resources encode H values (18 + steps H t a r)
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      after B H t a parents r es stack := by
  intro t r B
  rw [advance_add,PV_LIB_A_F6Counter11.history18]
  exact continuation C K P resources encode H values t a parents b r es stack

#print axioms threadStore
#print axioms panicStore
#print axioms steps
#print axioms after
#print axioms continuation
#print axioms history
end PV_LIB_A_F6EarlyHistory11
