import PV_LIB_A_RangeReply12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_RangeInvariant12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable

/-- Iterator facet at any actual loop iteration, rather than a fresh first
iteration assumption or an activation-counter identity across a callee. -/
def Iterator (s : Store Data) (a start finish : Nat) : Prop :=
  s.cells ⟨a,7,[]⟩ = some (PV_LIB_A_Range165.sourceRange start finish)

def next (start finish : Nat) := if start < finish then start+1 else start

def post (s : Store Data) (a : Nat) (parents : List Frame) (start finish : Nat) : Store Data :=
  let t := (PV_THR2_Source15Loop93Issue.pending s a parents).store
  if start < finish then write t ⟨a,7,[]⟩ (some (PV_LIB_A_Range165.sourceRange (start+1) finish)) else t

/-- Actual loop preparation only creates8/9/10 and its source references. -/
theorem prepared (s : Store Data) (a : Nat) (parents : List Frame) :
    (PV_THR2_Source15Loop93Issue.pending s a parents).store.cells ⟨a,7,[]⟩ = s.cells ⟨a,7,[]⟩ := by
  simp [PV_THR2_Source15Loop93Issue.pending,PV_THR2_Source15Loop93Prefix.pending,
    PV_THR2_Source15Loop93Prefix.prepared,PV_THR2_Source15Loop93Issue.prepared,
    PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write]

theorem post_iterator (s : Store Data) (a : Nat) (parents : List Frame) (start finish : Nat)
    (before : Iterator s a start finish) :
    Iterator (post s a parents start finish) a (next start finish) finish := by
  unfold post next Iterator
  by_cases live : start < finish
  · simp only [if_pos live,write_same]
  · simp only [if_neg live,prepared]
    exact before

/-- Every later iteration executes the same actual3447 poll. All replies are
retained on the updated store; no range value is reconstructed from a reply. -/
theorem poll (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (start finish : Nat) (before : Iterator s a start finish) :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
    let c := PV_THR2_Source15Loop93Issue.pending s a parents
    PV_LIB_A_DeferredActions.step B K (PV_LIB_A_RangePoll11.programs P) resources encode H values
      ⟨⟨⟨.running c,w,es⟩,stack⟩,none⟩ =
      sourceReceive B {c with store := post s a parents start finish} es stack
        (PV_LIB_A_RangePoll11.site s a) .done (H (PV_LIB_A_RangePoll11.site s a).waiting.request w) := by
  exact PV_LIB_A_RangePoll11.poll C K P resources encode H values s a parents b w es stack start finish
    (by rw [prepared]; exact before)

/-- Completion preserves the loop invariant at the saturated successor.
Pending retries retain this SAME store by RangeRetry11.retry. -/
theorem delivered (s : Store Data) (a : Nat) (parents : List Frame) (start finish : Nat) (v : Data)
    (before : Iterator s a start finish) :
    Iterator (PV_LIB_A_RangeReply12.deliveredStore s (post s a parents start finish) a parents v)
      a (next start finish) finish := by
  unfold Iterator
  rw [PV_LIB_A_RangeReply12.iterator]
  exact post_iterator s a parents start finish before

#print axioms Iterator
#print axioms next
#print axioms post
#print axioms prepared
#print axioms post_iterator
#print axioms poll
#print axioms delivered
end PV_LIB_A_RangeInvariant12
