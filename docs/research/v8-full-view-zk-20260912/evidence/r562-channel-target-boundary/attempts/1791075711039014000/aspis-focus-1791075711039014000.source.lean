import AspisV8R17.SourceOriginalWeights
import AspisV8R19.R561SparseGPairing

/-! Exact-field source-shaped channel boundary identity. This proves neither
native execution nor image coverage, probability, or full privacy. -/
set_option autoImplicit false
namespace AspisV8R19.R562
open AspisV8R17
open scoped BigOperators
variable {F : Type*} [Field F]

/-- The selected structured opening has zero claim whenever the three
retained point functionals, inactive balance, and both image tails vanish.
The literal tau updates remain in the source expression. -/
theorem structured_claim_zero (half : F)
    (points : Fin 3 → Fin 10 → F) (kappa : F)
    (inactive : Finset (Fin 1024)) (pivot : Fin 1024)
    (order : Fin 1024 ≃ Fin 1024) (mask : Fin 1024 → F)
    (q : Nat → F) (a b c tau : F)
    (hmask : let m := AspisV8R16.inverseTransport inactive pivot order
      (fun j => sourceChord half q a b c j.val)
       ∑ i, mask i*m i = 0)
    (hp1 : let m := AspisV8R16.inverseTransport inactive pivot order
      (fun j => sourceChord half q a b c j.val)
       sourcePointFunctional (points 1) m = 0)
    (hp2 : let m := AspisV8R16.inverseTransport inactive pivot order
      (fun j => sourceChord half q a b c j.val)
       sourcePointFunctional (points 2) m = 0)
    (hbalance : let m := AspisV8R16.inverseTransport inactive pivot order
      (fun j => sourceChord half q a b c j.val)
       ∑ i ∈ inactive, m i = 0)
    (htail : q 1023 = 0) (himage : b*q 1022-c*q 1021 = 0) :
    rangeDot 1024 (sourceQuotientWeights half
      (extendFin1024 (AspisV8R16.transportDual inactive pivot order
        (sourceOriginalWeight points kappa inactive mask true))) a b c tau true) q = 0 := by
  rw [original_weights_transported_pairing]
  simp only [Bool.true_eq, if_true, hmask, hp1, hp2, hbalance, htail, himage,
    mul_zero, add_zero]

/-- The full selected sparse coin order supplies the structured terminal
functional, without using the older dense power-row mixing model. -/
theorem structured_sparse_claim_zero (half : F)
    (points : Fin 3 → Fin 10 → F) (kappa : F)
    (q : Nat → F) (a b c tau : F) (z : RoundCoins F 10)
    (hmask : let m := AspisV8R16.inverseTransport
      AspisR19.TwoSwapSourceTable.inactive 1023 AspisR19.TwoSwapSourceTable.order
      (fun j => sourceChord half q a b c j.val)
      sourceMaskLoop half (R561.sparseSlices m 0)
        (literalMaskContributions 10
          (readRoundCoins 26 (R561.sparseSlices m) 10 1) z) = 0)
    (hp1 : let m := AspisV8R16.inverseTransport
      AspisR19.TwoSwapSourceTable.inactive 1023 AspisR19.TwoSwapSourceTable.order
      (fun j => sourceChord half q a b c j.val)
      sourcePointFunctional (points 1) m = 0)
    (hp2 : let m := AspisV8R16.inverseTransport
      AspisR19.TwoSwapSourceTable.inactive 1023 AspisR19.TwoSwapSourceTable.order
      (fun j => sourceChord half q a b c j.val)
      sourcePointFunctional (points 2) m = 0)
    (hbalance : let m := AspisV8R16.inverseTransport
      AspisR19.TwoSwapSourceTable.inactive 1023 AspisR19.TwoSwapSourceTable.order
      (fun j => sourceChord half q a b c j.val)
      ∑ i ∈ AspisR19.TwoSwapSourceTable.inactive, m i = 0)
    (htail : q 1023 = 0) (himage : b*q 1022-c*q 1021 = 0) :
    rangeDot 1024 (sourceQuotientWeights half
      (extendFin1024 (AspisV8R16.transportDual
        AspisR19.TwoSwapSourceTable.inactive 1023 AspisR19.TwoSwapSourceTable.order
        (sourceOriginalWeight points kappa AspisR19.TwoSwapSourceTable.inactive
          (AspisR19.TwoSwapSourceG.original (maskWeights271 half z)) true)))
      a b c tau true) q = 0 := by
  apply structured_claim_zero half points kappa
    AspisR19.TwoSwapSourceTable.inactive 1023 AspisR19.TwoSwapSourceTable.order
    (AspisR19.TwoSwapSourceG.original (maskWeights271 half z)) q a b c tau
  · dsimp only
    rw [R561.maskWeights_sparse_pairing]
    exact hmask
  · exact hp1
  · exact hp2
  · exact hbalance
  · exact htail
  · exact himage

#print axioms structured_claim_zero
#print axioms structured_sparse_claim_zero
end AspisV8R19.R562
