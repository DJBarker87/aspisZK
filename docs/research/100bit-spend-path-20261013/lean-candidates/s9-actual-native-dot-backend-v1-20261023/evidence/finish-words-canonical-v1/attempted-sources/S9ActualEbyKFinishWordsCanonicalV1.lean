import AspisR1S9ProductionPairCutV1.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualEbyKFinishWordsCanonicalV1
abbrev W := aspis_core.field.wide_exact.WideExact
def CanonicalWords (w : W) : Prop :=
  ((w.c0.c0.a.val<2147483647 ∧ w.c0.c0.b.val<2147483647) ∧
    (w.c0.c1.a.val<2147483647 ∧ w.c0.c1.b.val<2147483647)) ∧
  ((w.c1.c0.a.val<2147483647 ∧ w.c1.c0.b.val<2147483647) ∧
    (w.c1.c1.a.val<2147483647 ∧ w.c1.c1.b.val<2147483647))
private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B)
    (out : B) (h : (do let a ← m; f a) = .ok out) :
    ∃ a, m = .ok a ∧ f a = .ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok a => exact ⟨a,rfl,h⟩
private theorem bound (x : U32) (h : ¬ x ≥ aspis_core.field.P) : x.val<2147483647 := by
  unfold aspis_core.field.P at h
  change ¬ x.val ≥ 2147483647 at h
  omega

/-- Accepted actual from_limbs validates all eight SAME output words. -/
theorem from_limbs_some_canonical (limbs : Array U32 8#usize) (out : W)
    (h : aspis_core.field.wide_exact.WideExact.from_limbs limbs = .ok (some out)) :
    CanonicalWords out := by
  unfold aspis_core.field.wide_exact.WideExact.from_limbs at h
  obtain ⟨x0,hx0,h⟩ := bind_success _ _ _ h
  split at h
  · cases h
  · rename_i hb0
    obtain ⟨x1,hx1,h⟩ := bind_success _ _ _ h
    split at h
    · cases h
    · rename_i hb1
      obtain ⟨x2,hx2,h⟩ := bind_success _ _ _ h
      split at h
      · cases h
      · rename_i hb2
        obtain ⟨x3,hx3,h⟩ := bind_success _ _ _ h
        split at h
        · cases h
        · rename_i hb3
          obtain ⟨x4,hx4,h⟩ := bind_success _ _ _ h
          split at h
          · cases h
          · rename_i hb4
            obtain ⟨x5,hx5,h⟩ := bind_success _ _ _ h
            split at h
            · cases h
            · rename_i hb5
              obtain ⟨x6,hx6,h⟩ := bind_success _ _ _ h
              split at h
              · cases h
              · rename_i hb6
                obtain ⟨x7,hx7,h⟩ := bind_success _ _ _ h
                split at h
                · cases h
                · rename_i hb7
                  have he := Option.some.inj (Result.ok.inj h)
                  subst out
                  exact ⟨⟨⟨bound x0 hb0,bound x1 hb1⟩,⟨bound x2 hb2,bound x3 hb3⟩⟩,
                    ⟨⟨bound x4 hb4,bound x5 hb5⟩,⟨bound x6 hb6,bound x7 hb7⟩⟩⟩

/-- Universal arbitrary native accumulator state: successful actual finish
returns canonical words because the same from_limbs check accepted them.
No bounded-history, arithmetic-validity or independent child success premise. -/
theorem actual_finish_success_words_canonical (self : fast_pairing.EbyKDot) (out : W)
    (h : fast_pairing.EbyKDot.finish self = .ok out) : CanonicalWords out := by
  unfold fast_pairing.EbyKDot.finish at h
  obtain ⟨q0,hq0,h⟩ := bind_success _ _ _ h
  obtain ⟨limbs0,hlimbs0,h⟩ := bind_success _ _ _ h
  obtain ⟨a,ha,h⟩ := bind_success _ _ _ h
  obtain ⟨b,hb,h⟩ := bind_success _ _ _ h
  obtain ⟨c,hc,h⟩ := bind_success _ _ _ h
  obtain ⟨d,hd,h⟩ := bind_success _ _ _ h
  obtain ⟨q1,hq1,h⟩ := bind_success _ _ _ h
  obtain ⟨limbs1,hlimbs1,h⟩ := bind_success _ _ _ h
  obtain ⟨e,he,h⟩ := bind_success _ _ _ h
  obtain ⟨f,hf,h⟩ := bind_success _ _ _ h
  obtain ⟨g,hg,h⟩ := bind_success _ _ _ h
  obtain ⟨hh,hhh,h⟩ := bind_success _ _ _ h
  obtain ⟨o,hfrom,h⟩ := bind_success _ _ _ h
  cases o with
  | none => simp only [core.option.Option.unwrap] at h; cases h
  | some value =>
    have he : value=out := Result.ok.inj h
    subst out
    exact from_limbs_some_canonical _ value hfrom

#print axioms from_limbs_some_canonical
#print axioms actual_finish_success_words_canonical
end AspisR1S9ActualEbyKFinishWordsCanonicalV1
