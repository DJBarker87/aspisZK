import AspisV8R17.SourceChordTranspose

/-! Literal three weight updates after chord_transpose. No relation-image
premise is assumed for q; its two residuals remain on the right-hand side. -/
set_option autoImplicit false
namespace AspisV8R17
variable {F : Type*} [CommRing F]
open scoped BigOperators

def sourceImageUpdates (w : ℕ → F) (t tt b c : F) : ℕ → F :=
  Function.update (Function.update (Function.update w 1023 (w 1023+t))
    1022 (w 1022+tt*b)) 1021 (w 1021-tt*c)

theorem sourceImageUpdates_apply (w : ℕ → F) (t tt b c : F) (i : ℕ) :
    sourceImageUpdates w t tt b c i = w i + (if i=1023 then t else 0) +
      (if i=1022 then tt*b else 0) - (if i=1021 then tt*c else 0) := by
  by_cases h1 : i=1021
  · subst i; simp [sourceImageUpdates]
  by_cases h2 : i=1022
  · subst i; simp [sourceImageUpdates]
  by_cases h3 : i=1023
  · subst i; simp [sourceImageUpdates]
  simp [sourceImageUpdates, Function.update_of_ne, h1, h2, h3]

theorem sourceImageUpdates_dot (w q : ℕ → F) (t tt b c : F) :
    rangeDot 1024 (sourceImageUpdates w t tt b c) q =
      rangeDot 1024 w q + t*q 1023 + tt*(b*q 1022-c*q 1021) := by
  simp only [rangeDot, sourceImageUpdates_apply, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_range,
    show 1023<1024 from by decide, show 1022<1024 from by decide,
    show 1021<1024 from by decide, if_true]
  ring

def sourceQuotientWeights (half : F) (w : ℕ → F) (a b c tau : F)
    (structured : Bool) : ℕ → F :=
  sourceImageUpdates (sourceChordTranspose half w a b c)
    (if structured then tau^3 else tau) (if structured then tau^4 else tau^2) b c

theorem source_quotient_weights_pairing (half : F) (w q : ℕ → F)
    (a b c tau : F) (structured : Bool) :
    rangeDot 1024 (sourceQuotientWeights half w a b c tau structured) q =
      rangeDot 1024 w (sourceChord half q a b c) +
      (if structured then tau^3 else tau)*q 1023 +
      (if structured then tau^4 else tau^2)*(b*q 1022-c*q 1021) := by
  rw [sourceQuotientWeights, sourceImageUpdates_dot, ← source_chord_transpose_pairing]

theorem source_two_channel_weights_pairing (half : F) (wR wG qR qG : ℕ → F)
    (a b c tau : F) :
    rangeDot 1024 (sourceQuotientWeights half wR a b c tau false) qR +
      rangeDot 1024 (sourceQuotientWeights half wG a b c tau true) qG =
      rangeDot 1024 wR (sourceChord half qR a b c) +
      rangeDot 1024 wG (sourceChord half qG a b c) +
      tau*qR 1023 + tau^2*(b*qR 1022-c*qR 1021) +
      tau^3*qG 1023 + tau^4*(b*qG 1022-c*qG 1021) := by
  simp only [source_quotient_weights_pairing, Bool.false_eq_true,
    Bool.true_eq, if_false, if_true]
  ring

#print axioms sourceImageUpdates_apply
#print axioms sourceImageUpdates_dot
#print axioms source_quotient_weights_pairing
#print axioms source_two_channel_weights_pairing
end AspisV8R17
