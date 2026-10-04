import AspisV8R19.SourceEdgeGrowth
import AspisV8R19.ResidualModel

/-! The exceptional D31 direction is safe for the sparse G core because
the precise source carry schedule has no 62→64 or 63→*→64 path. Field
weights stay symbolic. No concrete polynomial recurrence is unfolded. -/
namespace AspisR19.HighQueryGCore
open AspisV8R17 SourceEdgeGrowth
variable {F : Type*} [CommRing F]

theorem no_single_path : 64 ∉ indexTargets 62 := by decide
theorem no_double_path : 64 ∉ (indexTargets 63).flatMap indexTargets := by decide

theorem boundary124 (half a b c : F) :
    sourceChord half (unitVector 124) a b c 128=0 := by
  rw [sourceChord_unit_even half 62 128 (by decide)]
  simp only [Nat.reduceMod,Nat.reduceDiv,↓reduceIte,
    sparseX_zero half 62 64 no_single_path]
  simp [unitVector]

theorem boundary127 (half a b c : F) :
    sourceChord half (unitVector 127) a b c 128=0 := by
  rw [sourceChord_unit_odd half 63 128 (by decide)]
  simp only [Nat.reduceMod,Nat.reduceDiv,↓reduceIte,
    sparseXX_zero half 63 64 no_double_path]
  simp [unitVector]

theorem sourceChord_support (half : F) (q : Nat → F) (n : Nat)
    (hq : ∀ r, 2*n ≤ r → q r=0) (a b c : F) (r : Nat) (hr : 2*n+3 ≤ r) :
    sourceChord half q a b c r=0 := by
  unfold sourceChord
  rw [finiteChordCoefficient_eq 512 _ _
    (fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2)
    (fun e he => (sourceEdges_bounds half 513 schedule513_bounded e he).2)]
  apply LowGResidualSupport.low_chord _ _
    (sourceEdges_growth half 512 growth512) (sourceEdges_growth half 513 growth513)
    _ n _ a b c r hr
  intro i hi
  by_cases hn : i<1024 <;> simp [zeroExtend,hn,hq i hi]

theorem unit_g_zero (half a b c : F) (j : Nat) (hj : j<112) (i : Fin 271) :
    sourceChord half (unitVector j) a b c (128+3*i.val)=0 := by
  apply sourceChord_support half _ 56 _ a b c _ (by omega)
  intro r hr
  simp [unitVector,show r ≠ j by omega]

def exceptional (alpha : F) (r : Nat) : F :=
  unitVector 127 r - alpha^3*unitVector 124 r

theorem exceptional_g_zero (half alpha a b c : F) (i : Fin 271) :
    sourceChord half (exceptional alpha) a b c (128+3*i.val)=0 := by
  by_cases hi : i.val=0
  · simp only [hi,mul_zero,add_zero]
    change sourceChord half (fun r => unitVector 127 r-alpha^3*unitVector 124 r) a b c 128=0
    rw [sourceChord_difference,boundary127,boundary124,mul_zero,sub_zero]
  · apply sourceChord_support half _ 64 _ a b c _ (by omega)
    intro r hr
    simp [exceptional,unitVector,show r ≠ 127 by omega,show r ≠ 124 by omega]

theorem low_repair_preserves_g (half : F) (q v : Nat → F)
    (same : ∀ r, 88 ≤ r → q r=v r) (a b c : F) (i : Fin 271) :
    sourceChord half q a b c (128+3*i.val)=sourceChord half v a b c (128+3*i.val) := by
  unfold sourceChord
  rw [finiteChordCoefficient_eq 512 _ _
    (fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2)
    (fun e he => (sourceEdges_bounds half 513 schedule513_bounded e he).2)]
  rw [finiteChordCoefficient_eq 512 _ _
    (fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2)
    (fun e he => (sourceEdges_bounds half 513 schedule513_bounded e he).2)]
  apply LowKernelSeparation.high_observation_retained _ _
    (sourceEdges_growth half 512 growth512) (sourceEdges_growth half 513 growth513)
    _ _ _ a b c _ (by omega)
  intro r hr
  by_cases hn : r<1024 <;> simp [zeroExtend,hn,same r hr]

#print axioms no_single_path
#print axioms no_double_path
#print axioms boundary124
#print axioms boundary127
#print axioms sourceChord_support
#print axioms unit_g_zero
#print axioms exceptional_g_zero
#print axioms low_repair_preserves_g
end AspisR19.HighQueryGCore
