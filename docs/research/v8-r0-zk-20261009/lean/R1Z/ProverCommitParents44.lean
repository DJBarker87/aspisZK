import R1Z.ProverCommitTrustedStd24
/-! D156 parent collection. BTreeSet is used only through its one named
collect/iterate law. Exact ordered list equality transports an arbitrary
stateful continuation, including lazy missing-child coins and the retained
subsequent coin state; equality of sets alone would not suffice. -/
set_option autoImplicit false
namespace R1Z.ProverCommitParents44
open ProverCommitTrustedStd24
variable {Value State Thread Slot Output Acc : Type}
variable {cmp : Nat → Nat → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
variable [DecidableEq Thread]
variable (map : MapAPI Nat Value State cmp) (tls : TLSAPI Thread Slot Output)
  (thread : Thread) (schedule : List (Thread × ProverCommitTLS23.Access Slot Output))
  (trusted : TrustedStd map tls thread schedule)

def input (entries : List (Nat × Value)) : List Nat := entries.map (fun entry => entry.1 / 2)

def native (state : State) : List Nat := map.set_from_iter (input (map.entries state))

def model (entries : List (Nat × Value)) : List Nat := ascendingDistinct (input entries)

include trusted

theorem exact_order (state : State) :
    native map state = model (map.decode state).toList := by
  rw [native, trusted.btree_set_from_iter_ordered, trusted.btree_iter_ordered]
  rfl

theorem ascending (state : State) : (native map state).Pairwise (· ≤ ·) := by
  rw [exact_order map tls thread schedule trusted]
  exact Finset.pairwise_sort (input (map.decode state).toList).toFinset (· ≤ ·)

theorem duplicate_free (state : State) : (native map state).Nodup := by
  rw [exact_order map tls thread schedule trusted]
  exact Finset.sort_nodup (input (map.decode state).toList).toFinset (· ≤ ·)

theorem parent_iff (state : State) (p : Nat) :
    p ∈ native map state ↔ ∃ entry ∈ (map.decode state).toList, entry.1 / 2 = p := by
  rw [exact_order map tls thread schedule trusted]
  simp only [model, ascendingDistinct, Finset.mem_sort, List.mem_toFinset, input, List.mem_map]

/-- Every accumulator component and every ordered callback invocation agrees.
No distributional or freshness hypothesis is needed for this deterministic
transport. In particular Acc may contain the full retained coin tape. -/
theorem traversal (state : State) (step : Acc → Nat → Acc) (initial : Acc) :
    (native map state).foldl step initial =
      (model (map.decode state).toList).foldl step initial := by
  rw [exact_order map tls thread schedule trusted]

/-- An arbitrary subsequent observer of the complete state is preserved. -/
theorem continuation {Result : Type} (state : State) (step : Acc → Nat → Acc)
    (initial : Acc) (observe : Acc → Result) :
    observe ((native map state).foldl step initial) =
      observe ((model (map.decode state).toList).foldl step initial) := by
  rw [traversal map tls thread schedule trusted]

#print axioms exact_order
#print axioms ascending
#print axioms duplicate_free
#print axioms parent_iff
#print axioms traversal
#print axioms continuation
end R1Z.ProverCommitParents44
