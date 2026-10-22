import OraclePortS10CFG

/-! Strict occurrence order on the extracted CFG paths. The result supplies
an earlier occurrence, including paths that revisit a block; it does not
identify Rust state transitions with oracle-program semantics. -/
set_option autoImplicit false
namespace AspisR1.OraclePortS10StrictOrder
open OraclePortS10CFG

def BeforeEnd (cut target : Nat) (visits : List Nat) : Prop :=
  ∃ pre post, visits = pre ++ cut :: (post ++ [target])

theorem path_suffix {edge : Nat → Nat → Prop} {root target : Nat}
    {visits : List Nat} (path : Path edge root target visits) :
    ∃ init, visits = init ++ [target] := by
  cases path with
  | start => exact ⟨[], rfl⟩
  | step path step => exact ⟨_, rfl⟩

theorem before_end {edge : Nat → Nat → Prop} {root cut target : Nat}
    (dominates : Dominates edge root cut target) (distinct : cut ≠ target)
    {visits : List Nat} (path : Path edge root target visits) :
    BeforeEnd cut target visits := by
  obtain ⟨init, shape⟩ := path_suffix path
  have member := dominates visits path
  rw [shape] at member
  have earlier : cut ∈ init := by
    rcases List.mem_append.mp member with h | h
    · exact h
    · exact False.elim (distinct (List.mem_singleton.mp h))
  obtain ⟨pre, post, split⟩ := List.append_of_mem earlier
  refine ⟨pre, post, ?_⟩
  rw [shape, split]
  simp only [List.append_assoc, List.cons_append]

#print axioms path_suffix
#print axioms before_end
end AspisR1.OraclePortS10StrictOrder
