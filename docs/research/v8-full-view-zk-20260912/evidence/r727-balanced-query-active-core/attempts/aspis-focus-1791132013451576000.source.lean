import AspisV8R19.R720QueryActiveCoreImage
import AspisV8R19.R699SourceTopChordBoundary

set_option autoImplicit false
namespace AspisV8R19.R727TopBalance
open AspisV8R17 AspisV8R16 AspisR19
open HighRepairInvariant R662FullIndexedMaskPreservation
open R699SourceTopChordBoundary R720QueryActiveCoreImage
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2:F)]

theorem sourceChord_last (half a b c : F) (q : Nat → F) :
    sourceChord half q a b c 1023 = c*q 1022+a*q 1023+b*q 1020 := by
  unfold sourceChord
  rw [finiteChordCoefficient_eq 512 _ _
    (fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2)
    (fun e he => (sourceEdges_bounds half 513 schedule513_bounded e he).2)]
  simp only [chordCoefficient, show 1023%2=1 by rfl, if_neg (by decide : ¬1023%2=0),
    show 1023/2=511 by rfl, chordOdd]
  rw [scatter_512_511]
  simp [zeroExtend]

theorem indexed_balance_from_top (half a b c : F) (q : Index 256 → F)
    (h20 : flattenFull q 1020=0) (h22 : flattenFull q 1022=0)
    (h23 : flattenFull q 1023=0) :
    (∑ r ∈ TwoSwapSourceTable.inactive, indexedMask half a b c q r)=0 := by
  have ht := congrFun (transport_inverse TwoSwapSourceTable.inactive 1023
    TwoSwapSourceTable.pivot_inactive TwoSwapSourceTable.order
    (fun j : Fin 1024 => sourceChord half (flattenFull q) a b c j.val)) (1023:Fin 1024)
  change transport TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
    (indexedMask half a b c q) 1023 = sourceChord half (flattenFull q) a b c 1023 at ht
  rw [transport, TwoSwapSourceTable.pivot_fixed, if_pos rfl] at ht
  rw [ht, sourceChord_last, h20, h22, h23]
  ring

#print axioms sourceChord_last
#print axioms indexed_balance_from_top
end
end AspisV8R19.R727TopBalance
