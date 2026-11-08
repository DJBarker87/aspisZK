import PV_LIB_A_RangeCaptures12
import PV_LIB_A_RangeRetry11
import PV_THR2_ChildReturnedLocal
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_RangeReply12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

/-- Delivery writes only actual child local0 and saved caller local8. The
incoming store already includes93's iterator write, including on retries. -/
def returnedStore (c : Config) (site : SourceSite) (v : Data) :=
  match site.waiting.action with
  | .child child _ => write (write c.store ⟨child,0,[]⟩ (some v)) ⟨c.frame.activation,8,[]⟩ (some v)
  | _ => c.store

def deliveredStore (s t : Store Data) (a : Nat) (parents : List Frame) (v : Data) :=
  returnedStore {PV_THR2_Source15Loop93Issue.pending s a parents with store := t}
    (PV_LIB_A_RangePoll11.site s a) v

theorem returned (C : Carrier OWNER Data) (s t : Store Data) (a : Nat)
    (parents : List Frame) (v : Data) (w : OWNER)
    (es events : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    sourceReceive C {PV_THR2_Source15Loop93Issue.pending s a parents with store := t}
      es stack (PV_LIB_A_RangePoll11.site s a) .done ⟨.returned (.ok v),w,events⟩ =
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.block47.drop 6, loops := PV_LIB_A_RangeMatch12.loops},parents,deliveredStore s t a parents v⟩,
        w,es ++ events⟩,stack⟩,none⟩ := by
  unfold sourceReceive
  change (let q := PV_THR2_ChildBoundary.delivered C ({PV_THR2_Source15Loop93Issue.pending s a parents with store := t}) (PV_LIB_A_RangePoll11.site s a).waiting ⟨.returned (.ok v),w,events⟩; (⟨⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩,none⟩ : SourceState)) = _
  rw [PV_THR2_ChildReturnedLocal.delivered C _ _
    (PV_THR2_Source15Loop93Issue.prepared s a).nextActivation 8 v w events (by rfl)]
  rfl

def steps (C : Carrier OWNER Data) (K : Control) (s t : Store Data) (a : Nat)
    (parents : List Frame) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) : Nat :=
  match r.answer with
  | .returned (.ok v) => 2 + PV_THR2_Source15LiveCaptures.steps C K (deliveredStore s t a parents v) a r.world
  | _ => 0

def after (C : Carrier OWNER Data) (K : Control) (s t : Store Data) (a : Nat)
    (parents : List Frame) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) : SourceState :=
  match r.answer with
  | .returned (.ok v) => ⟨PV_THR2_Source15LiveCaptures.after C K
      (deliveredStore s t a parents v) a parents r.world (es ++ r.events) stack,none⟩
  | _ => sourceReceive C {PV_THR2_Source15Loop93Issue.pending s a parents with store := t}
      es stack (PV_LIB_A_RangePoll11.site s a) .done r

/-- Every93 reply is retained. On return execute actual3448/3460 and Some's
captures or None's break on the SAME already-written store. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s t : Store Data) (a : Nat) (parents : List Frame)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) :
    advance C K P resources encode H values (steps C K s t a parents r)
      (sourceReceive C {PV_THR2_Source15Loop93Issue.pending s a parents with store := t}
        es stack (PV_LIB_A_RangePoll11.site s a) .done r) =
      after C K s t a parents es stack r := by
  rcases r with ⟨answer,w,events⟩
  cases answer with
  | pending => rfl
  | fault f => rfl
  | returned result =>
    cases result with
    | fail e => rfl
    | div => rfl
    | ok v =>
      unfold steps after
      rw [returned,advance_add,PV_LIB_A_RangeMatch12.run,
        PV_LIB_A_RangeCaptures12.run]

/-- Delivery cannot rewrite the actual iterator cell. This carries the
post-poll invariant across child completion without an activation equality. -/
theorem iterator (s t : Store Data) (a : Nat) (parents : List Frame) (v : Data) :
    (deliveredStore s t a parents v).cells ⟨a,7,[]⟩ = t.cells ⟨a,7,[]⟩ := by
  simp [deliveredStore,returnedStore,PV_LIB_A_RangePoll11.site,
    PV_THR2_StaticReply.wait,write]

#print axioms returnedStore
#print axioms deliveredStore
#print axioms returned
#print axioms steps
#print axioms after
#print axioms run
#print axioms iterator
end PV_LIB_A_RangeReply12
