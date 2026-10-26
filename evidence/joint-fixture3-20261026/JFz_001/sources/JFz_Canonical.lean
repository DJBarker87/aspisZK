import Op4P_Refinement
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_Canonical
open AspisV8R19.DuplexFrames OraclePortCompactDraft

theorem nil : canonical [] := by
  constructor
  · rfl
  · intro j hj
    simp only [List.length_nil, Nat.zero_div, List.mem_range] at hj
    omega

/-- Four-byte induction; evaluation of each numeral is confined to one word. -/
theorem cons4 (a b c d : Fin 256) (tail : Bytes)
    (word : little [a,b,c,d] < 2147483647) (rest : canonical tail) :
    canonical (a::b::c::d::tail) := by
  rcases rest with ⟨multiple, valid⟩
  constructor
  · simp only [List.length_cons]
    omega
  · intro j hj
    simp only [List.mem_range, List.length_cons] at hj
    cases j with
    | zero => simpa only [Nat.mul_zero, slice, List.drop_zero,
        List.take_succ_cons, List.take_zero] using word
    | succ j =>
      have hj' : j ∈ List.range (tail.length / 4) := by
        simp only [List.mem_range]
        omega
      have h := valid j hj'
      simpa only [slice, Nat.mul_succ, List.drop_succ_cons] using h

#print axioms nil
#print axioms cons4
end AspisR1.JFz_Canonical
end
