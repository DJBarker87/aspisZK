import NDO_JFr_BlockWindow
set_option autoImplicit false
namespace AspisR1.JFu_FlatWindow

theorem source {α : Type} (xs : List (List α))
    (lengths : ∀ c ∈ xs,c.length=32) (i : Nat) (bound : i<xs.length) :
    ((xs.flatten.drop (32*i)).take 16)=(xs[i]'bound).take 16 := by
  induction xs generalizing i with
  | nil => simp at bound
  | cons head tail ih =>
    have headLength : head.length=32 := lengths head (by simp)
    have tailLengths : ∀ c ∈ tail,c.length=32 := by
      intro c hc
      exact lengths c (by simp only [List.mem_cons];exact Or.inr hc)
    cases i with
    | zero =>
      simp only [Nat.mul_zero,List.drop_zero,List.flatten_cons,List.getElem_cons_zero,List.take_append,
        headLength,show 16-32=0 from rfl,List.take_zero,List.append_nil]
    | succ i =>
      rw [List.flatten_cons,List.drop_append,headLength]
      have skip : 32≤32*(i+1) := by omega
      rw [List.drop_eq_nil_of_le (by rw [headLength];omega),List.nil_append]
      rw [show 32*(i+1)-32=32*i from by omega]
      exact ih tailLengths i (by simpa using bound)

#print axioms source
end AspisR1.JFu_FlatWindow
