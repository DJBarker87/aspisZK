import R1Z.ProverRwFullFuns
import R1Z.ProverCommitArrayIndex25
import R1Z.ProverRwSamplerArithmetic

/-! The actual rewritten query membership loop is a bounded ordered scan.
No external operation, success premise or concrete 22-cell reduction is used. -/
set_option autoImplicit false
namespace R1Z.ProverRwQueryContains
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
abbrev Queries := Array U32 22#usize

def search (accepted : Queries) (candidate : U32) : Nat → Usize → Option Bool
  | 0,_ => none
  | fuel+1,index =>
    if accepted.val[index.val]? = some candidate then some true
    else search accepted candidate fuel (Usize.wrapping_add index 1#usize)

theorem loop_search (accepted : Queries) (candidate : U32)
    (n index : Usize) (fuel : Nat) (bound : index.val+fuel=n.val)
    (size : n.val ≤ 22) :
    host_transcript.query_contains_loop accepted n candidate index =
      ok (search accepted candidate fuel index) := by
  unfold host_transcript.query_contains_loop
  induction fuel generalizing index with
  | zero =>
    have stop : ¬ index < n := by change ¬ index.val < n.val; omega
    rw [loop]
    simp only [host_transcript.query_contains_loop.body,stop,if_false,bind_tc_ok,search]
  | succ fuel ih =>
    have go : index < n := by change index.val < n.val; omega
    have hi : index.val < (22#usize).val := by change index.val < 22; omega
    have hidx := ProverCommitArrayIndex25.array_index_usize_ok accepted index hi
    have hlen : index.val < accepted.val.length := by simpa [accepted.property] using hi
    have add : (Usize.wrapping_add index 1#usize).val = index.val+1 := by
      rw [Usize.wrapping_add_val_eq]
      have one : (1#usize).val = 1 := rfl
      rw [one,Nat.mod_eq_of_lt]
      have hn := n.hSize
      change n.val < UScalar.size .Usize at hn
      omega
    by_cases equal : accepted.val[index.val] = candidate
    · rw [loop]
      simp only [host_transcript.query_contains_loop.body,go,if_true,hidx,bind_tc_ok,
        search,List.getElem?_eq_getElem hlen,Option.some.injEq,equal,if_true]
    · rw [loop]
      simp only [host_transcript.query_contains_loop.body,go,if_true,hidx,bind_tc_ok,
        search,List.getElem?_eq_getElem hlen,Option.some.injEq,equal,if_false,lift]
      exact ih _ (by omega)

def contains (accepted : Queries) (n : Usize) (candidate : U32) : Bool :=
  (search accepted candidate n.val 0#usize).getD false

theorem contains_exact (accepted : Queries) (n : Usize) (candidate : U32)
    (size : n.val ≤ 22) :
    host_transcript.query_contains accepted n candidate = ok (contains accepted n candidate) := by
  unfold host_transcript.query_contains contains
  rw [loop_search accepted candidate n 0#usize n.val (by change 0+n.val=n.val; omega) size]
  cases search accepted candidate n.val 0#usize <;> rfl

#print axioms loop_search
#print axioms contains_exact
end R1Z.ProverRwQueryContains
