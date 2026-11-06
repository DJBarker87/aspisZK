import NJI_Array64
import NHY_ArrayExt
set_option autoImplicit false
noncomputable section
namespace NJI_CheckpointLoop
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
abbrev Words := Array U64 8#usize
def capacity : U64 := 1048576#u64
def ValidPrefix (a : Words) (k : Nat) : Prop :=
 ∀ j, j<k → j<8 → NHY_ArrayExt.coord a j≤capacity

/-- K021: the arbitrary-coordinate modifies set, including the write BEFORE a
failed capacity check. This is a local sequence buffer, not an account write. -/
def Frame (before after target : Words) (k : Nat) : Prop :=
 ∀ j, j<8 → NHY_ArrayExt.coord after j=
  if j=k then NHY_ArrayExt.coord target k else NHY_ArrayExt.coord before j

theorem written_step (before after target : Words) (k : Nat) (bound : k<8)
 (pre : NHY_ArrayExt.Prefix before target k) (frame : Frame before after target k) :
 NHY_ArrayExt.Prefix after target (k+1) := by
 intro j hj hwidth
 rw [frame j hwidth]
 by_cases same : j=k
 · subst j;simp
 · simp only [same,ite_false]
   exact pre j (by omega) hwidth

theorem valid_step (before after target : Words) (k : Nat)
 (pre : ValidPrefix before k) (frame : Frame before after target k)
 (accepted : NHY_ArrayExt.coord target k≤capacity) : ValidPrefix after (k+1) := by
 intro j hj hwidth
 rw [frame j hwidth]
 by_cases same : j=k
 · subst j;simpa using accepted
 · simp only [same,ite_false]
   exact pre j (by omega) hwidth

/-- Complete eight-cell reconstruction uses the existing generic extensionality
law. No concrete recurrence or unrolled whole-buffer kernel proof. -/
theorem finished (after target : Words)
 (pre : NHY_ArrayExt.Prefix after target 8) : after=target :=
 NHY_ArrayExt.whole after target pre

inductive ScanResult where | accepted | invalid
deriving DecidableEq

/-- Each loaded word is retained in the trace, including the rejecting word;
the rejected suffix is never read. -/
def scan : List U64 → List U64 × ScanResult
 | [] => ([],.accepted)
 | x::xs =>
   if x>capacity then ([x],.invalid)
   else let (trace,result):=scan xs;(x::trace,result)

theorem first_error (xs : List U64) :
 (scan xs).2=if xs.any (fun x => decide (x>capacity)) then .invalid else .accepted := by
 induction xs with
 | nil => rfl
 | cons x xs ih =>
   by_cases h : x>capacity
   · have hx : decide (x>capacity)=true := by exact decide_eq_true h
     simp only [scan,if_pos h,List.any_cons,hx,Bool.true_or,ite_true]
   · have hx : decide (x>capacity)=false := by exact decide_eq_false h
     simpa only [scan,if_neg h,List.any_cons,hx,Bool.false_or] using ih

theorem abort_prefix (xs : List U64) : ∃ suffix, (scan xs).1++suffix=xs := by
 induction xs with
 | nil => exact ⟨[],rfl⟩
 | cons x xs ih =>
   by_cases h : x>capacity
   · exact ⟨xs,by simp [scan,h]⟩
   · obtain ⟨suffix,same⟩:=ih
     exact ⟨suffix,by simpa [scan,h] using congrArg (List.cons x) same⟩

#print axioms written_step
#print axioms valid_step
#print axioms finished
#print axioms first_error
#print axioms abort_prefix
end NJI_CheckpointLoop
