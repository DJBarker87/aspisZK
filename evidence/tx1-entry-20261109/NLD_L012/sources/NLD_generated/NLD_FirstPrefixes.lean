import NLD_FirstDecoded
import NLD_FoldLaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLD
open Aeneas Aeneas.Std Result
/-- A source action, not a proposed native frame certificate. -/
def tx1Reply (ops : AdapterRw.Ops) (p : Public) (pub proof : Bytes) (k : Usize) :=
  ops.op10 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops) p pub proof k () none

def firstEvents (s : ParentState) : List Event :=
  [⟨.observer,s,s⟩,⟨.tx1,s,s⟩]
def errorEvents (s : ParentState) : List Event := firstEvents s ++ [⟨.errorMap,s,s⟩]

/-- Child outer failure retains the attempted call and has no mapper suffix. -/
theorem first_fail (ops : AdapterRw.Ops) (p : Public) (pub proof : Bytes)
    (k : Usize) (s : ParentState) (e : Error)
    (reply : tx1Reply ops p pub proof k = .fail e) :
    run (firstDecoded ops p pub proof k) s = (.fail e,s,firstEvents s) := by
  unfold firstDecoded AdapterRw.observer
  change ops.op10 _ p pub proof k () none = .fail e at reply
  simp only [run,reply,firstEvents]

theorem first_div (ops : AdapterRw.Ops) (p : Public) (pub proof : Bytes)
    (k : Usize) (s : ParentState)
    (reply : tx1Reply ops p pub proof k = .div) :
    run (firstDecoded ops p pub proof k) s = (.div,s,firstEvents s) := by
  unfold firstDecoded AdapterRw.observer
  change ops.op10 _ p pub proof k () none = .div at reply
  simp only [run,reply,firstEvents]

/-- Returning Ok carries the SAME owned Vec, without a success-only root. -/
theorem first_ok (ops : AdapterRw.Ops) (p : Public) (pub proof : Bytes)
    (k : Usize) (s : ParentState) (checkpoint : Vec)
    (reply : tx1Reply ops p pub proof k = .ok (.Ok checkpoint)) :
    run (firstDecoded ops p pub proof k) s = (.ok (.Ok checkpoint),s,firstEvents s) := by
  unfold firstDecoded AdapterRw.observer
  change ops.op10 _ p pub proof k () none = .ok (.Ok checkpoint) at reply
  simp only [run,reply,firstEvents]

/-- Error mapping is attempted exactly once, even when its own model aborts. -/
theorem first_error (ops : AdapterRw.Ops) (p : Public) (pub proof : Bytes)
    (k : Usize) (s : ParentState) (e : VE)
    (reply : tx1Reply ops p pub proof k = .ok (.Err e)) :
    run (firstDecoded ops p pub proof k) s =
      ((do let mapped ← (BuiltinFnOnce VE PE).call_once ops.op44 e
           ok (core.result.Result.Err mapped)),s,errorEvents s) := by
  unfold firstDecoded AdapterRw.observer
  change ops.op10 _ p pub proof k () none = .ok (.Err e) at reply
  simp only [run,reply,errorEvents,firstEvents]
  cases (BuiltinFnOnce VE PE).call_once ops.op44 e <;> rfl

/-- Unconditional source cut producer. It supplies no native-to-source law,
no TX1:094 packet, and therefore no entry row root. -/
theorem first_source_fold (ops : AdapterRw.Ops) (p : Public) (pub proof : Bytes)
    (k : Usize) (s : ParentState) :
    Cuts (firstDecoded ops p pub proof k) s
      (AdapterRw.first_decoded ops p pub proof k) s
      (run (firstDecoded ops p pub proof k) s).2.2 := by
  have h := cuts_from_run (firstDecoded ops p pub proof k) s
  rw [firstDecoded_erasure,firstDecoded_source_frame] at h
  exact h
#print axioms first_fail
#print axioms first_div
#print axioms first_ok
#print axioms first_error
#print axioms first_source_fold
end AspisR1.NLD
