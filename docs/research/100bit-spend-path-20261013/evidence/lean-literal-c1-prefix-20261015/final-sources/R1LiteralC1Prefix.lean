import R1LiteralTranscript

/-! The C1 projection is unchanged when a transcript prefix is extended by its
current indexed message. This is list-index plumbing only. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralC1Prefix

open AspisR1.LiteralTranscript

theorem c1At_take_current
    (rs : List (Message × Challenge)) (i : Nat) (hi : i < rs.length)
    (c : Challenge) :
    c1At (rs.take i ++ [(rs[i].1, c)]) = c1At rs := by
  by_cases hzero : i = 0
  · subst i
    simp only [List.take_zero, List.nil_append, c1At,
      List.getElem?_cons_zero, List.getElem?_eq_getElem hi, Option.bind_some]
  · have hpos : 0 < i := Nat.pos_of_ne_zero hzero
    have htake : 0 < (rs.take i).length := by
      simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
      omega
    have hleft := c1At_append (rs.take i) [(rs[i].1, c)] htake
    have hright := c1At_append (rs.take i) (rs.drop i) htake
    rw [List.take_append_drop] at hright
    calc
      c1At (rs.take i ++ [(rs[i].1, c)]) = c1At (rs.take i) := hleft
      _ = c1At rs := hright.symm

#print axioms c1At_take_current

end AspisR1.LiteralC1Prefix
end
