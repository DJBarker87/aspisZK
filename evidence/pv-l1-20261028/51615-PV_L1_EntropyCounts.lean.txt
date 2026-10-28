import PV_L1_EntropyProducer
set_option autoImplicit false
noncomputable section
namespace PV_L1_EntropyCounts
open Aeneas Aeneas.Std Result
open R1Z ProverRwRng ProverRwRngControl ProverRwRngOwnerEvents
open SideChannelL1AttemptRecord (Event)
open PV_L1_EntropyProducer
variable [ErasureFns]

def callIndices (events : List Event) : List Nat :=
  events.filterMap fun | .call .rng n => some n | _ => none

def returns (events : List Event) : List SideChannelL1AttemptRecord.IOStatus :=
  events.filterMap fun | .rngReturn s => some s | _ => none

theorem indices (p : Tape) (n : Nat) :
    callIndices (drawEvents p n) = List.range' p.used.val n := by
  unfold drawEvents callIndices
  generalize List.range' p.used.val n = xs
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [List.flatMap_cons,List.filterMap_append,List.filterMap_cons,List.filterMap_nil]; exact congrArg (List.cons i) ih
#print axioms indices

theorem return_statuses (p : Tape) (n : Nat) :
    returns (drawEvents p n) = (List.range' p.used.val n).map
      (fun i => statusOf p.replies.val[i]?) := by
  unfold drawEvents returns
  generalize List.range' p.used.val n = xs
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [List.flatMap_cons,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,List.map_cons]; exact congrArg (List.cons _) ih
#print axioms return_statuses

theorem draw_count (p : Tape) (n : Nat) : (returns (drawEvents p n)).length = n := by
  rw [return_statuses,List.length_map,List.length_range']
#print axioms draw_count

theorem source_count (nonce : Array U8 32#usize) (p after : Tape) (status : Status)
    (executed : owner nonce p = ok (after,status)) :
    (returns (drawEvents p (after.used.val-p.used.val))).length ≤ 16 ∧
    callIndices (drawEvents p (after.used.val-p.used.val)) =
      List.range' p.used.val (after.used.val-p.used.val) := by
  obtain ⟨states,_,_,cursor,bound,_⟩ := source_replay nonce p after status executed
  rw [draw_count,indices]
  exact ⟨by omega,rfl⟩
#print axioms source_count
end PV_L1_EntropyCounts
