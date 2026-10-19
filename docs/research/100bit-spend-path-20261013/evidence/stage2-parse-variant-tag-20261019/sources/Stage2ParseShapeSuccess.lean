import Stage2ParseShapeExplicitOps
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Stage2AdoptedParseShape.ParseShapeSuccess
private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem successful_variant (ops : ParseShapeOps) (proof : Slice U8)
    (variant : transport.Variant)
    (h : verifier.candidate.parse_shape ops proof = ok (.Ok variant)) :
    variant = transport.Variant.S2 := by
  unfold verifier.candidate.parse_shape at h
  obtain ⟨size, _, h⟩ := bind_success _ _ _ h
  split at h
  · cases h
  · obtain ⟨header, _, h⟩ := bind_success _ _ _ h
    obtain ⟨badMagic, _, h⟩ := bind_success _ _ _ h
    cases badMagic with
    | true => simp only [↓reduceIte] at h; cases h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨tag, _, h⟩ := bind_success _ _ _ h
      simp only [transport.Variant.tag, bind_tc_ok] at h
      split at h
      · cases h
      · obtain ⟨tail, _, h⟩ := bind_success _ _ _ h
        obtain ⟨iter, _, h⟩ := bind_success _ _ _ h
        obtain ⟨pair, _, h⟩ := bind_success _ _ _ h
        rcases pair with ⟨badTail, _⟩
        cases badTail with
        | true => cases h
        | false =>
          cases h
          rfl

theorem successful_variant_tag (ops : ParseShapeOps) (proof : Slice U8)
    (variant : transport.Variant)
    (h : verifier.candidate.parse_shape ops proof = ok (.Ok variant)) :
    transport.Variant.tag variant = ok 2#u8 := by
  rw [successful_variant ops proof variant h]
  rfl
#print axioms successful_variant
#print axioms successful_variant_tag
end AspisR1Stage2AdoptedParseShape.ParseShapeSuccess
