import AspisR1Publish32.Funs
import AspisR1IndexInsert32.Funs
set_option autoImplicit false
namespace R1Z.ProverCommitPublication32
open Aeneas Aeneas.Std Result
abbrev Bytes := alloc.vec.Vec U8
abbrev IndexMap := alloc.vec.Vec (Usize × Bytes)

/-- A bounded vector cursor cannot wrap before its last element. -/
theorem next_cursor {T : Type} (table : alloc.vec.Vec T) (pos : Usize)
    (h : pos.val < table.val.length) :
    (Usize.wrapping_add pos 1#usize).val = pos.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  have bound := table.property
  have size := Usize.max_succ_eq_pow
  have one : (1#usize).val = 1 := by scalar_tac
  have nowrap : pos.val+1 < UScalar.size .Usize := by
    rw [UScalar.size_def, UScalarTy.Usize_numBits_eq]
    omega
  rw [one, Nat.mod_eq_of_lt nowrap]

/-- Lookup on every finite owned table terminates without an indexing error.
Sortedness is needed for the map interpretation, but not for this totality fact. -/
theorem lookup_total (fuel : Nat) (table : IndexMap) (key pos : Usize)
    (hi : pos.val ≤ table.val.length) (hf : table.val.length-pos.val < fuel) :
    ∃ value, AspisR1Publish32.sim.owned32.index_get table key pos = ok value := by
  induction fuel generalizing pos with
  | zero => omega
  | succ fuel ih =>
    rw [AspisR1Publish32.sim.owned32.index_get]
    by_cases done : pos = alloc.vec.Vec.len table
    · simp only [done,if_true]
      exact ⟨none,rfl⟩
    · have more : pos.val < table.val.length := by
        have ne : pos.val ≠ table.val.length := by
          intro eq
          apply done
          apply UScalar.eq_of_val_eq
          exact eq
        omega
      obtain ⟨entry,hr,_⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec table pos more)
      have step := next_cursor table pos more
      obtain ⟨value,ht⟩ := ih (Usize.wrapping_add pos 1#usize) (by omega) (by omega)
      rcases entry with ⟨k,v⟩
      simp only [done,if_false,alloc.vec.Vec.index_slice_index,hr,bind_tc_ok,BuiltinClone]
      by_cases eq : key = k
      · simp only [eq,if_true]
        exact ⟨some v,rfl⟩
      · simp only [eq,if_false]
        by_cases lt : key < k
        · simp only [lt,if_true]
          exact ⟨none,rfl⟩
        · simp only [lt,if_false,lift,bind_tc_ok,ht]
          exact ⟨value,rfl⟩

def lookup (key : Usize) : List (Usize × Bytes) → Option Bytes
  | [] => none
  | (k,v)::xs => if key=k then some v else if key<k then none else lookup key xs

/-- Exact ordered-association-list lookup, for all table sizes and byte values.
Repeated query keys therefore return the same last-replacement value. -/
theorem lookup_refines (fuel : Nat) (table : IndexMap) (key pos : Usize)
    (hi : pos.val ≤ table.val.length) (hf : table.val.length-pos.val < fuel) :
    AspisR1Publish32.sim.owned32.index_get table key pos =
      ok (lookup key (table.val.drop pos.val)) := by
  induction fuel generalizing pos with
  | zero => omega
  | succ fuel ih =>
    rw [AspisR1Publish32.sim.owned32.index_get]
    by_cases done : pos = alloc.vec.Vec.len table
    · have hp : pos.val = table.val.length := congrArg UScalar.val done
      simp only [if_pos done,List.drop_eq_nil_of_le (by omega : table.val.length ≤ pos.val),lookup]
    · have more : pos.val < table.val.length := by
        have ne : pos.val ≠ table.val.length := by
          intro eq
          apply done
          apply UScalar.eq_of_val_eq
          exact eq
        omega
      obtain ⟨entry,hr,he⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec table pos more)
      have hd : table.val.drop pos.val = entry :: table.val.drop (pos.val+1) := by
        rw [he]
        exact List.drop_eq_getElem_cons more
      have step := next_cursor table pos more
      have tail := ih (Usize.wrapping_add pos 1#usize) (by omega) (by omega)
      rw [step] at tail
      rcases entry with ⟨k,v⟩
      simp only [done,if_false,alloc.vec.Vec.index_slice_index,hr,bind_tc_ok,BuiltinClone,hd,lookup]
      by_cases eq : key = k
      · simp only [eq,if_true]
      · simp only [eq,if_false]
        by_cases lt : key < k
        · simp only [lt,if_true]
        · simp only [lt,if_false,lift,bind_tc_ok,tail]

theorem clone_vec {T : Type} (v : alloc.vec.Vec T) :
    alloc.vec.CloneVec.clone (BuiltinClone T) v = ok v := by
  obtain ⟨out,hr,he⟩ := WP.spec_imp_exists
    (Slice.clone_spec (s := v) (clone := (BuiltinClone T).clone) (by intros;rfl))
  exact hr.trans (congrArg (fun x : alloc.vec.Vec T => Result.ok x) he.symm)

/-- The observation order is the query list, including repetitions, rather
than the sorted order used when constructing the commitment leaves. Byte
append failure is retained exactly; missing entries return none. -/
def publish (opened : List (Usize × Bytes)) : List U32 → Bytes → Result (Option Bytes)
  | [], out => ok (some out)
  | q::qs, out =>
    match lookup (UScalar.cast .Usize q) opened with
    | none => ok none
    | some bytes => do
      let next ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out (alloc.vec.Vec.deref bytes)
      publish opened qs next

/-- Exact finite-list semantics of the extracted query-publication owner,
for every finite input and every byte value; no source-call success premise. -/
theorem publish_refines (fuel : Nat) (queries : alloc.vec.Vec U32)
    (opened : IndexMap) (pos : Usize) (out : Bytes)
    (hi : pos.val ≤ queries.val.length) (hf : queries.val.length-pos.val < fuel) :
    AspisR1Publish32.sim.owned32.publish_queries queries opened pos out =
      publish opened.val (queries.val.drop pos.val) out := by
  induction fuel generalizing pos out with
  | zero => omega
  | succ fuel ih =>
    rw [AspisR1Publish32.sim.owned32.publish_queries]
    by_cases done : pos = alloc.vec.Vec.len queries
    · have hp : pos.val = queries.val.length := congrArg UScalar.val done
      simp only [if_pos done,List.drop_eq_nil_of_le (by omega : queries.val.length ≤ pos.val),publish]
    · have more : pos.val < queries.val.length := by
        have ne : pos.val ≠ queries.val.length := by
          intro eq
          apply done
          apply UScalar.eq_of_val_eq
          exact eq
        omega
      obtain ⟨q,hr,he⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec queries pos more)
      have hd : queries.val.drop pos.val = q :: queries.val.drop (pos.val+1) := by
        rw [he]
        exact List.drop_eq_getElem_cons more
      have step := next_cursor queries pos more
      have get := lookup_refines (opened.val.length+1) opened (UScalar.cast .Usize q) 0#usize
        (by scalar_tac) (by scalar_tac)
      simp only [UScalar.ofNatCore_val_eq,List.drop_zero] at get
      simp only [if_neg done,clone_vec,bind_tc_ok,alloc.vec.Vec.index_slice_index,hr,lift,get,
        hd,publish]
      cases found : lookup (UScalar.cast .Usize q) opened.val with
      | none => rfl
      | some bytes =>
        simp only [bind_tc_ok]
        cases appended : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
            (alloc.vec.Vec.deref bytes) with
        | fail e => simp only [bind_tc_fail]
        | div => simp only [bind_tc_div]
        | ok next =>
          simp only [bind_tc_ok]
          have tail := ih (Usize.wrapping_add pos 1#usize) next (by omega) (by omega)
          rw [step] at tail
          exact tail

#print axioms clone_vec
#print axioms publish_refines
#print axioms lookup_refines
#print axioms next_cursor
#print axioms lookup_total
end R1Z.ProverCommitPublication32
