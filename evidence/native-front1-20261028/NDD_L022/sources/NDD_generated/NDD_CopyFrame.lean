import KMX_CopyMeaning
set_option autoImplicit false
namespace NDD_CopyFrame
open KMX_CopyMeaning

theorem one_step {α : Type} (src dst : Nat → α) (i k : Nat) :
    loop src dst i 1 k = if k = i then src i else dst k := by
  rw [loop_spec]
  by_cases h : k = i
  · subst k; simp
  · have hn : ¬ (i ≤ k ∧ k < i + 1) := by omega
    simp [h,hn]

theorem padded_prefix {α : Type} (src : Nat → α) (zero : α) (n k : Nat) :
    loop src (fun _ => zero) 0 n k = if k < n then src k else zero :=
  copy_prefix src (fun _ => zero) n k

theorem disjoint_compose {α : Type} (src dst : Nat → α) (start n m : Nat) :
    loop src (loop src dst start n) (start+n) m = loop src dst start (n+m) := by
  funext k
  simp only [loop_spec]
  by_cases a : start+n ≤ k ∧ k < start+n+m
  · have b : start ≤ k ∧ k < start+(n+m) := by omega
    simp [a,b]
  · by_cases b : start ≤ k ∧ k < start+n
    · have c : start ≤ k ∧ k < start+(n+m) := by omega
      simp [a,b,c]
    · have c : ¬(start ≤ k ∧ k < start+(n+m)) := by omega
      simp [a,b,c]

#print axioms one_step
#print axioms padded_prefix
#print axioms disjoint_compose
end NDD_CopyFrame
