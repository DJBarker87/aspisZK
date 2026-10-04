import AspisV8R19.R720QueryActiveCoreImage
import AspisV8R19.R699SourceTopChordBoundary

set_option autoImplicit false
namespace AspisV8R19.R727TopBalance
open AspisV8R17 AspisV8R16 AspisR19
open HighRepairInvariant R662FullIndexedMaskPreservation
open R699SourceTopChordBoundary R720QueryActiveCoreImage
open R710SelectedActivePolynomial R707FullActiveDeterminant
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2:F)]

theorem sourceChord_last (half a b c : F) (q : Nat → F) :
    sourceChord half q a b c 1023 = c*q 1022+a*q 1023+b*q 1021 := by
  unfold sourceChord
  rw [finiteChordCoefficient_eq 512 _ _
    (fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2)
    (fun e he => (sourceEdges_bounds half 513 schedule513_bounded e he).2)]
  simp only [chordCoefficient, show 1023%2=1 by rfl, if_neg (by decide : ¬1023%2=0),
    show 1023/2=511 by rfl, chordOdd]
  rw [scatter_512_511]
  simp [zeroExtend]

theorem indexed_balance_from_top (half a b c : F) (q : Index 256 → F)
    (h21 : flattenFull q 1021=0) (h22 : flattenFull q 1022=0)
    (h23 : flattenFull q 1023=0) :
    (∑ r ∈ TwoSwapSourceTable.inactive, indexedMask half a b c q r)=0 := by
  have ht := congrFun (transport_inverse TwoSwapSourceTable.inactive 1023
    TwoSwapSourceTable.pivot_inactive TwoSwapSourceTable.order
    (fun j : Fin 1024 => sourceChord half (flattenFull q) a b c j.val)) (1023:Fin 1024)
  change transport TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
    (indexedMask half a b c q) 1023 = sourceChord half (flattenFull q) a b c 1023 at ht
  rw [transport, TwoSwapSourceTable.pivot_fixed, if_pos rfl] at ht
  rw [ht, sourceChord_last, h21, h22, h23]
  ring

theorem balanced_query_active_core_image (half alpha u v0 : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (target : J → F)
    (good : MvPolynomial.eval (activeAssignment alpha u v0) (polyMinor half).det ≠ 0) :
    ∃ q : Index 256 → F,
      (∀ i, sourceChord half (flattenFull q) (1+u*v0) (u*v0-1) (-(u+v0))
        (rowCode i) = target i) ∧
      (∀ slot : Fin 4, ∀ root : Fin 22,
        R682FullQueryNormalization.evaluate256 (fun d => q (d,slot)) (t root) = 0) ∧
      (∀ d : Fin 256, R370KernelEvaluation.firstFold 256 alpha q d = 0) ∧
      (∑ r ∈ TwoSwapSourceTable.inactive,
        indexedMask half (1+u*v0) (u*v0-1) (-(u+v0)) q r)=0 ∧
      flattenFull q 1020 = 0 ∧ flattenFull q 1021 = 0 ∧
      flattenFull q 1022 = 0 ∧ flattenFull q 1023 = 0 := by
  obtain ⟨q,hr,hquery,hfold,h20,h21,h22,h23⟩ :=
    query_active_core_image half alpha u v0 t ht target good
  exact ⟨q,hr,hquery,hfold,
    indexed_balance_from_top half (1+u*v0) (u*v0-1) (-(u+v0)) q h21 h22 h23,
    h20,h21,h22,h23⟩

#print axioms sourceChord_last
#print axioms indexed_balance_from_top
#print axioms balanced_query_active_core_image
end
end AspisV8R19.R727TopBalance
