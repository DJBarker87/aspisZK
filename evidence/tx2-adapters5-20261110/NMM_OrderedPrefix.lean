import NMM_LaneSymbolic
import Init.Data.List.Range
set_option autoImplicit false
set_option pp.proofs false
namespace NMM_OrderedPrefix

/-- A local counter checked at every event determines its entire order,
including an early stopped prefix; no post-abort heap is a parameter. -/
theorem complete (events : List Nat)
 (checked : ∀ i, ∀ hi : i < events.length, events[i]'hi = i) :
 events = List.range events.length := by
 apply List.ext_getElem?
 intro i
 by_cases hi : i < events.length
 · have bound : i < (List.range events.length).length := by simpa only [List.length_range] using hi
   rw [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem bound]
   simp only [List.getElem_range,checked i hi]
 · have length : (List.range events.length).length=events.length := by simp only [List.length_range]
   rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]

theorem next (n : Nat) : List.range n ++ [n] = List.range (n+1) := by
 rw [List.range_succ]

theorem bounded_prefix (events : List Nat)
 (checked : ∀ i, ∀ hi : i < events.length, events[i]'hi = i)
 (bound : events.length ≤ 21) :
 ∃ n, n ≤ 21 ∧ events = List.range n :=
 ⟨events.length,bound,complete events checked⟩

#print complete
#print axioms complete
#print next
#print axioms next
#print bounded_prefix
#print axioms bounded_prefix
end NMM_OrderedPrefix
