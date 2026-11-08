import PV_LIB_A_F124EntryData14
import PV_FN_THREAD_f124_ReturnedPost
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F124ReturnedFrame14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f124_StorePost

/-- CLOSED124's explicit returned source store frames every older foreign cell,
except the actual return destination. The theorem is applied by name; no
callee body, OWNER projection or equality of activation counters is assumed. -/
theorem source_frame {E : Type} (x : Input E) (strong weak : Data) (q : Address)
    (older : q.activation < x.s.nextActivation) (foreign : q.activation ≠ x.a)
    (destination : q ≠ (⟨x.parent.activation,x.dest,[]⟩ : Address)) :
    (PV_FN_THREAD_f124_ReturnedPost.store x strong weak).cells q = x.s.cells q :=
  caller_frame x strong weak _ _ _ _ _ q older foreign destination

/-- Only monotonicity crosses the callee boundary. The existing exact counter
formula is consumed internally, never required as a caller preservation premise. -/
theorem counter_mono {E : Type} (x : Input E) (strong weak : Data) :
    x.s.nextActivation ≤ (PV_FN_THREAD_f124_ReturnedPost.store x strong weak).nextActivation := by
  change x.s.nextActivation ≤ x.s.nextActivation+9
  omega

/-- Preserve the complete saved-frame numbering, including pending child
bounds, by the named monotonicity lemma at the explicit returned Post store.
This is a source-store fact, not Full/v2/context execution transport. -/
theorem stack_numbering {E : Type} (x : Input E) (strong weak : Data) (ceiling : Nat)
    (frames : List Frame) (h : PV_STX2_LiveNumbering.StackBelow x.s.nextActivation ceiling frames) :
    PV_STX2_LiveNumbering.StackBelow
      (PV_FN_THREAD_f124_ReturnedPost.store x strong weak).nextActivation ceiling frames :=
  PV_STX2_LiveNumbering.stack_mono h (counter_mono x strong weak)

theorem numbered {E : Type} (x : Input E) (strong weak : Data) (c : Config)
    (h : PV_STX2_LiveNumbering.Numbered {c with store := x.s}) :
    PV_STX2_LiveNumbering.Numbered
      {c with store := PV_FN_THREAD_f124_ReturnedPost.store x strong weak} :=
  ⟨Nat.lt_of_lt_of_le h.1 (counter_mono x strong weak),
   PV_STX2_LiveNumbering.waiting_mono h.2.1 (counter_mono x strong weak),
   stack_numbering x strong weak c.frame.activation c.callers h.2.2⟩

/-- The actual returned source layout and the foreign frame are obtained from
CLOSED124's named Post. OWNER, bytes, original-entry reachability and the full
LoopInvariant are deliberately absent from this source-only result. -/
theorem post_and_frame {E : Type} (x : Input E) (strong weak : Data)
    (fresh : x.a < x.s.nextActivation) (parent : x.parent.activation < x.s.nextActivation) :
    PV_FN_THREAD_f124_ReturnedPost.Post x strong weak ∧
    (∀ q : Address, q.activation < x.s.nextActivation → q.activation ≠ x.a →
      q ≠ (⟨x.parent.activation,x.dest,[]⟩ : Address) →
      (PV_FN_THREAD_f124_ReturnedPost.store x strong weak).cells q = x.s.cells q) :=
  ⟨PV_FN_THREAD_f124_ReturnedPost.properties x strong weak fresh parent,
   fun q older foreign destination => source_frame x strong weak q older foreign destination⟩

#print axioms source_frame
#print axioms counter_mono
#print axioms stack_numbering
#print axioms numbered
#print axioms post_and_frame
end PV_LIB_A_F124ReturnedFrame14
