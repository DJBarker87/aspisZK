import AspisV8R17.SourceOriginalWeights
import Mathlib.Tactic.Ring

/-! Exact-field source-shaped channel boundary identity. This proves neither
native execution nor image coverage, probability, or full privacy. -/
set_option autoImplicit false
namespace AspisV8R19.R562
open AspisV8R17
open scoped BigOperators
variable {F : Type*} [CommRing F]

/-- The selected structured opening has zero claim whenever the three
retained point functionals, inactive balance, and both image tails vanish.
The literal tau updates remain in the source expression. -/
theorem structured_claim_zero (half : F)
    (points : Fin 3 → Fin 10 → F) (kappa : F)
    (inactive : Finset (Fin 1024)) (pivot : Fin 1024)
    (order : Fin 1024 ≃ Fin 1024) (mask : Fin 1024 → F)
    (q : Nat → F) (a b c tau : F)
    (hmask : let m := AspisV8R16.inverseTransport inactive pivot order
      (fun j => sourceChord half q a b c j.val); ∑ i, mask i*m i = 0)
    (hp1 : let m := AspisV8R16.inverseTransport inactive pivot order
      (fun j => sourceChord half q a b c j.val); sourcePointFunctional (points 1) m = 0)
    (hp2 : let m := AspisV8R16.inverseTransport inactive pivot order
      (fun j => sourceChord half q a b c j.val); sourcePointFunctional (points 2) m = 0)
    (hbalance : let m := AspisV8R16.inverseTransport inactive pivot order
      (fun j => sourceChord half q a b c j.val); ∑ i ∈ inactive, m i = 0)
    (htail : q 1023 = 0) (himage : b*q 1022-c*q 1021 = 0) :
    rangeDot 1024 (sourceQuotientWeights half
      (extendFin1024 (AspisV8R16.transportDual inactive pivot order
        (sourceOriginalWeight points kappa inactive mask true))) a b c tau true) q = 0 := by
  rw [original_weights_transported_pairing]
  simp only [Bool.true_eq, if_true, hmask, hp1, hp2, hbalance, htail, himage,
    mul_zero, add_zero]

/-- All beta values are allowed. Retaining the original rest claim, the
structured G claim, and p2 makes the combined target boundary zero.
Scale is an explicit parameter (the caller uses gamma^(-27)). -/
theorem channel_target_boundary (wr wg rest g : Nat → F) (beta scale : F)
    (hrest : rangeDot 1024 wr rest = 0)
    (hstructured : rangeDot 1024 wg g = 0)
    (hp2 : rangeDot 1024 (fun i => wg i-wr i) g =
      scale*rangeDot 1024 (fun i => wg i-wr i) rest) :
    beta*rangeDot 1024 (fun i => (1-beta)*wr i+beta*wg i) g +
      (1-beta)*scale*rangeDot 1024 (fun i => (1-beta)*wr i+beta*wg i) rest = 0 := by
  have diff (v : Nat → F) :
      rangeDot 1024 (fun i => wg i-wr i) v =
        rangeDot 1024 wg v-rangeDot 1024 wr v := by
    simp only [rangeDot, sub_mul, Finset.sum_sub_distrib]
  have blend (v : Nat → F) :
      rangeDot 1024 (fun i => (1-beta)*wr i+beta*wg i) v =
        (1-beta)*rangeDot 1024 wr v+beta*rangeDot 1024 wg v := by
    simp only [rangeDot, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
  rw [diff, diff, hrest, hstructured, sub_zero, zero_sub] at hp2
  have hg : rangeDot 1024 wr g = -(scale*rangeDot 1024 wg rest) :=
    neg_eq_iff_eq_neg.mp hp2
  rw [blend, blend, hrest, hstructured, hg]
  ring

#print axioms structured_claim_zero
#print axioms channel_target_boundary
end AspisV8R19.R562
