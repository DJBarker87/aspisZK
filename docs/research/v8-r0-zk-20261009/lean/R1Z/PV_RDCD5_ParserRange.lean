import R1Z.PV_RDCD4_SliceRange194
set_option autoImplicit false
namespace R1Z.PV_RDCD5_ParserRange
open Aeneas Aeneas.Std Result
/-- Checked Rust range indexing panics on either invalid bound. This parser
helper corrects the old arrayOutOfBounds carrier without erasing errors. -/
def index {T : Type} (xs : List T) (start stop : Nat) : Result (List T) :=
  if start ≤ stop ∧ stop ≤ xs.length then
    ok (PV_RDCD4_SliceRange194.window xs start stop)
  else fail .panic

theorem success {T : Type} (xs : List T) (start stop : Nat)
    (ordered : start ≤ stop) (bounded : stop ≤ xs.length) :
    index xs start stop = ok (PV_RDCD4_SliceRange194.window xs start stop) := by
  simp only [index,ordered,bounded,and_self,if_true]

theorem oversized {T : Type} (xs : List T) (start stop : Nat)
    (invalid : xs.length < stop) : index xs start stop = fail .panic := by
  simp only [index,show ¬stop ≤ xs.length from by omega,and_false,if_false]

/-- Exact Result transport through the existing range-index operation, including
its panic constructor. No successful-input restriction is present. -/
theorem binding {T : Type} (s : Slice T) (a b : Usize) :
    (do let out ← core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice T) s {start:=a, «end»:=b}
        ok out.val) = index s.val a.val b.val := by
  simp only [core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index,index,
    Slice.length,PV_RDCD4_SliceRange194.window,List.slice]
  split <;> rfl
#print axioms success
#print axioms oversized
#print axioms binding
end R1Z.PV_RDCD5_ParserRange
