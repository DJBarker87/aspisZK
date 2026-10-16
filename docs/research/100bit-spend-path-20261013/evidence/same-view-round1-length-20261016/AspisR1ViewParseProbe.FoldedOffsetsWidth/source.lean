import AspisR1ViewParseProbe.CleanParameterizedParse

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1ViewParseProbe.FoldedOffsetsWidth

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem add_val {a b c : Usize}
    (h : UScalar.add a b = Result.ok c) : c.val = a.val + b.val := by
  have he := UScalar.add_equiv a b
  have h' : (a + b : Result Usize) = Result.ok c := by
    change UScalar.add a b = Result.ok c
    exact h
  rw [h'] at he
  exact he.2.1

theorem folded_offsets_round1_width (base start finish used : Usize)
    (h : verifier.folded_offsets base true =
      Result.ok (some base, start, finish, used)) :
    finish.val - start.val = 224 := by
  unfold verifier.folded_offsets at h
  obtain ⟨i, hi, h⟩ := bind_success _ _ _ h
  obtain ⟨j, hj, h⟩ := bind_success _ _ _ h
  have ht : (some base, i, j, 256#usize) = (some base, start, finish, used) := Result.ok.inj h
  simp only [Prod.mk.injEq, Option.some.injEq] at ht
  rcases ht with ⟨_, his, hjf, _⟩
  subst start
  subst finish
  have hi' : i.val = base.val + 32 := add_val hi
  have hj' : j.val = base.val + 256 := add_val hj
  omega

#print axioms folded_offsets_round1_width

end AspisR1ViewParseProbe.FoldedOffsetsWidth
