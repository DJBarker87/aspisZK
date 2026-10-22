import MultiproofConeLiveBatch

set_option autoImplicit false
namespace AspisR1.MultiproofConeLiveFold
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConeLiveOrder MultiproofConeLiveLeaves MultiproofConeLivePreservation MultiproofConeLiveBatch

abbrev Leaf := U32 × Array U8 32#usize

/-- Structural iteration of the actual extracted leaf insertion. Hashing and
opening selection occur before each insertion in the source; their ordered
oracle program is a separate refinement obligation. -/
def fold : List Leaf → reference.Scratch → Result (Option reference.Scratch)
  | [],s => ok (some s)
  | (index,digest)::rest,s => do
      let out ← reference.leaf_step s index digest
      match out with
      | none => ok none
      | some next => fold rest next

theorem fold_projection (leaves : List Leaf) (s next : reference.Scratch)
    (room : s.n.val+leaves.length≤16) (success : fold leaves s=ok (some next)) :
    (keys next,next.n.val)=build (leaves.map (fun x => x.1.val)) (keys s) s.n.val := by
  induction leaves generalizing s with
  | nil => cases success;rfl
  | cons leaf rest ih =>
    rcases leaf with ⟨index,digest⟩
    simp only [fold] at success
    cases row : reference.leaf_step s index digest with
    | fail error => simp only [row,bind_tc_fail] at success;cases success
    | div => simp only [row,bind_tc_div] at success;cases success
    | ok out =>
      rw [row] at success
      simp only [bind_tc_ok] at success
      cases out with
      | none => cases success
      | some after =>
        have projection := leaf_projection s index digest (by simp at room;omega) after row
        have count : after.n.val≤s.n.val+1 := by
          have second := congrArg Prod.snd projection
          change after.n.val=(MultiproofConeLiveLeaves.insert (keys s) s.n.val index.val).2 at second
          unfold MultiproofConeLiveLeaves.insert at second
          split at second <;> simp_all
        have remaining : after.n.val+rest.length≤16 := by simp at room;omega
        simpa only [List.map_cons,build,←projection] using ih after remaining success

/-- Complete successful insertion-loop order on any nondecreasing stream,
with no distinct-query, digest-consistency or successful-hash hypothesis. -/
theorem fold_sorted (leaves : List Leaf) (s next : reference.Scratch)
    (empty : s.n.val=0) (room : leaves.length≤16)
    (sorted : (leaves.map (fun x => x.1.val)).Pairwise (·≤·))
    (success : fold leaves s=ok (some next)) : Strict (keys next) 0 next.n.val := by
  have projection := fold_projection leaves s next (by omega) success
  have first := congrArg Prod.fst projection
  have second := congrArg Prod.snd projection
  rw [empty] at first second
  change keys next=(build (leaves.map (fun x => x.1.val)) (keys s) 0).1 at first
  change next.n.val=(build (leaves.map (fun x => x.1.val)) (keys s) 0).2 at second
  rw [first,second]
  exact empty_build_sorted _ _ sorted

/-- The sortedness of the key prefix is proved by the actual extracted sort,
not assumed. The leaf-to-key projection is the explicit caller adapter checked
per iteration by the leaf/key P6 gates, still to be bound to stored openings. -/
theorem sorted_batch (input : Array U64 16#usize) (count : Usize) (bound : count.val≤16)
    (scratch : reference.Scratch) (empty : scratch.n.val=0) :
    ∃ ordered, MultiproofSortRef.sort_reference.sort_rows input 0#usize count=ok ordered ∧
      ∀ (leaves : List Leaf) (next : reference.Scratch), leaves.length≤16 →
      leaves.map (fun x => x.1.val)=(ordered.val.take count.val).map (fun x => x.val/256) →
      fold leaves scratch=ok (some next) → Strict (keys next) 0 next.n.val := by
  obtain ⟨ordered,eqout,_,sorted,_⟩ := MultiproofConeSortTotal.sort_rows_total
    count.val input 0#usize count (by simp) bound (by simp)
  refine ⟨ordered,eqout,?_⟩
  intro leaves next room projection success
  apply fold_sorted leaves scratch next empty room _ success
  rw [projection]
  exact projected_keys_sorted _ sorted

#print axioms fold_projection
#print axioms fold_sorted
#print axioms sorted_batch
end AspisR1.MultiproofConeLiveFold
