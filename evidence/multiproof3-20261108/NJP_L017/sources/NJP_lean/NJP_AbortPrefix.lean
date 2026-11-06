import NJP_LoopModel

set_option autoImplicit false
noncomputable section
namespace NJP_AbortPrefix
open Aeneas Aeneas.Std Result NJP_RowModel
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Successful replies before a runtime abort, plus the pending request.
There is no invented Rust Err arm or reply for the aborting syscall. -/
def pending {α : Type} (H : Request → Digest) :
    Nat → Program Request Digest α → Option (List (Request × Digest) × Request)
 | 0,.done _ => none
 | 0,.ask q _ => some ([],q)
 | n+1,.done _ => none
 | n+1,.ask q next => (pending H n (next (H q))).map fun (history,last) => ((q,H q)::history,last)

theorem exact_prefix {α : Type} (H : Request → Digest) (n : Nat)
    (p : Program Request Digest α) (history : List (Request × Digest)) (last : Request)
    (aborted : pending H n p=some (history,last)) :
    history=(eval H p).1.take n  ∧  history.length=n  ∧ 
    ((eval H p).1[n]?).map Prod.fst=some last := by
 induction n generalizing p history last with
 | zero =>
   cases p with
   | done x => simp only [pending] at aborted; contradiction
   | ask q next =>
     have same := Option.some.inj aborted
     cases same
     simp [eval]
 | succ n ih =>
   cases p with
   | done x => simp only [pending] at aborted; contradiction
   | ask q next =>
     simp only [pending] at aborted
     cases found : pending H n (next (H q)) with
     | none => simp only [found,Option.map_none] at aborted;contradiction
     | some pair =>
       obtain ⟨tail,request⟩ := pair
       simp only [found,Option.map_some] at aborted
       have same := Option.some.inj aborted
       cases same
       obtain ⟨tail_eq,tail_length,last_eq⟩ := ih (next (H q)) tail last found
       simp only [eval,List.take_succ_cons,List.length_cons,List.getElem?_cons_succ]
       exact ⟨congrArg (List.cons (q,H q)) tail_eq,by omega,last_eq⟩

theorem occupied_pending (H : Request → Digest) (nodes : Nat → U8) (length : Nat)
    (s : Scratch) (i w : Nat) (active : i<s.n) (both : paired s i) :
 pending H 0 (node nodes length s i w)=some ([],occupiedRequest s i) := by
 simp only [node,if_pos active,if_pos both,pending]

theorem sibling_pending (H : Request → Digest) (nodes : Nat → U8) (length : Nat)
    (s : Scratch) (i w : Nat) (active : i<s.n) (single : ¬paired s i)
    (available : s.cursor+32 ≤ length) :
 pending H 0 (node nodes length s i w)=some ([],siblingRequest s i nodes) := by
 simp only [node,if_pos active,if_neg single,if_pos available,pending]

#print exact_prefix
#print axioms exact_prefix
#print occupied_pending
#print axioms occupied_pending
#print sibling_pending
#print axioms sibling_pending
end NJP_AbortPrefix
end
