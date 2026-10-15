import R1GenericNoHit

/-! Indexed-round consequences of the generic no-hit predicate. These are
list facts only and make no probability or protocol-specific claim. -/
set_option autoImplicit false

namespace AspisR1.GenericNoHitIndex

open AspisR1.GenericNoHit

variable {X M C : Type}

theorem not_bad_at_index_from
    (bad : FS.Prefix X M C → M → C → Prop) (x : X)
    (prev : List (M × C)) :
    ∀ (rs : List (M × C)) (i : Nat) (hi : i < rs.length),
      ¬ hitFrom bad x prev rs →
      ¬ bad ⟨x, prev ++ rs.take i⟩ (rs[i]'hi).1 (rs[i]'hi).2 := by
  intro rs
  induction rs generalizing prev with
  | nil =>
      intro i hi
      omega
  | cons item rest ih =>
      rcases item with ⟨m, c⟩
      intro i hi hno
      cases i with
      | zero =>
          intro hbad
          apply hno
          simp only [hitFrom]
          exact Or.inl (by simpa using hbad)
      | succ i =>
          have hi' : i < rest.length := by omega
          have htail : ¬ hitFrom bad x (prev ++ [(m, c)]) rest := by
            intro htail
            apply hno
            simp only [hitFrom]
            exact Or.inr (by simpa [List.append_assoc] using htail)
          have hnext := ih (prev ++ [(m, c)]) i hi' htail
          have hpref : prev ++ ((m, c) :: rest).take (i + 1) =
              (prev ++ [(m, c)]) ++ rest.take i := by
            simp [List.append_assoc]
          have hidx : ((m, c) :: rest)[i + 1]'hi = rest[i]'hi' := by
            simp
          rw [hpref, hidx]
          exact hnext

theorem not_bad_at_index
    (bad : FS.Prefix X M C → M → C → Prop) (x : X)
    (rs : List (M × C)) (i : Nat) (hi : i < rs.length)
    (hno : ¬ hitFrom bad x [] rs) :
    ¬ bad ⟨x, rs.take i⟩ (rs[i]'hi).1 (rs[i]'hi).2 := by
  simpa using not_bad_at_index_from bad x [] rs i hi hno

theorem noHit_take
    (bad : FS.Prefix X M C → M → C → Prop) (x : X)
    (rs : List (M × C)) (n : Nat)
    (hno : ¬ hitFrom bad x [] rs) :
    ¬ hitFrom bad x [] (rs.take n) := by
  have hsplit := hitFrom_append bad x [] (rs.take n) (rs.drop n)
  have hdecomp : rs.take n ++ rs.drop n = rs := List.take_append_drop n rs
  intro hprefix
  apply hno
  rw [← hdecomp]
  exact hsplit.mpr (Or.inl hprefix)

#print axioms not_bad_at_index_from
#print axioms not_bad_at_index
#print axioms noHit_take

end AspisR1.GenericNoHitIndex
