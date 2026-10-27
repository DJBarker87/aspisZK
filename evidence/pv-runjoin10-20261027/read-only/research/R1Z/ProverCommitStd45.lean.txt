import R1Z.ProverCommitTrustedStd24
import Mathlib.Data.List.Destutter
/-! D157 scalar sort/dedup and map length. These transport complete ordered
consumers and error branches; no source caller or allocation law is added. -/
set_option autoImplicit false
namespace R1Z.ProverCommitStd45
open ProverCommitTrustedStd24
variable {Value State Thread Slot Output Acc : Type}
variable {cmp : Nat → Nat → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
variable [DecidableEq Thread]
variable (map : MapAPI Nat Value State cmp) (tls : TLSAPI Thread Slot Output)
  (thread : Thread) (schedule : List (Thread × ProverCommitTLS23.Access Slot Output))
  (trusted : TrustedStd map tls thread schedule)

def indices (xs : List Nat) : List Nat := map.vec_dedup (map.slice_sort xs)
def sortedDistinct (xs : List Nat) : List Nat := (xs.mergeSort (· ≤ ·)).dedup
include trusted

theorem sort_dedup (xs : List Nat) : indices map xs = sortedDistinct xs := by
  rw [indices,trusted.slice_sort_ascending,trusted.vec_dedup_adjacent]
  exact (List.pairwise_mergeSort' (· ≤ ·) xs).destutter_eq_dedup

theorem ascending (xs : List Nat) : (indices map xs).Pairwise (· ≤ ·) := by
  rw [sort_dedup map tls thread schedule trusted]
  exact (List.pairwise_mergeSort' (· ≤ ·) xs).sublist (List.dedup_sublist _)

theorem duplicate_free (xs : List Nat) : (indices map xs).Nodup := by
  rw [sort_dedup map tls thread schedule trusted]
  exact List.nodup_dedup _

theorem mem_indices (xs : List Nat) (x : Nat) : x ∈ indices map xs ↔ x ∈ xs := by
  rw [sort_dedup map tls thread schedule trusted]
  simp only [sortedDistinct,List.mem_dedup,List.mem_mergeSort]

/-- The multiproof consumer receives exactly the same ordered list, retaining
its result/error and every state component in Acc. -/
theorem consumer {Result : Type} (xs : List Nat) (consume : List Nat → Acc → Result)
    (initial : Acc) : consume (indices map xs) initial = consume (sortedDistinct xs) initial := by
  rw [sort_dedup map tls thread schedule trusted]

/-- Native len agrees with the ordered iteration used at publication. -/
theorem length_entries (s : State) : map.len s = (map.entries s).length := by
  rw [trusted.btree_len,trusted.btree_iter_ordered]

omit trusted

def rootGuard [DecidableEq Value] (level : State) (root : Value) : Bool :=
  map.len level == 1 && map.get level 0 == some root

include trusted

/-- Both outcomes of the short-circuit Merkle guard are transported; no
reachable-root success premise is smuggled into the library contract. -/
theorem root_guard [DecidableEq Value] (level : State) (root : Value) :
    rootGuard map level root = rootGuard modelMap (map.decode level) root := by
  simp only [rootGuard,trusted.btree_len,trusted.btree_get,modelMap]

theorem root_return [DecidableEq Value] {Result Error : Type} (level : State)
    (root : Value) (success : Result) (merkle : Error) :
    (if rootGuard map level root then Except.ok success else Except.error merkle) =
      (if rootGuard modelMap (map.decode level) root then Except.ok success else Except.error merkle) := by
  rw [root_guard map tls thread schedule trusted]

#print axioms sort_dedup
#print axioms ascending
#print axioms duplicate_free
#print axioms mem_indices
#print axioms consumer
#print axioms length_entries
#print axioms root_guard
#print axioms root_return
end R1Z.ProverCommitStd45
