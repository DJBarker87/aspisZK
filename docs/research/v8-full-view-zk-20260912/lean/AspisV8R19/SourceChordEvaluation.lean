import AspisV8R19.SourceNaturalShift
import AspisV8R17.ChordDual
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.LinearCombination

/-! Evaluate the actual finite 512/513 chord lanes in the maintained natural
basis. Both OOD zeros follow from the secant equation, without extra generic
rank assumptions. Interleaved evaluator/Rust field refinement is separate. -/
namespace AspisR19.SourceChordEvaluation
open AspisV8R17 AspisCircleTensorBinding SourceNaturalShift
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem gather_scale (half s : F) (w : Nat → F) (j : Nat) :
    sourceGather half (fun r => s*w r) j=s*sourceGather half w j := by
  simp only [sourceGather,mul_left_comm _ s,List.sum_map_mul_left]

theorem gather_congr (half : F) (w v : Nat → F) (j : Nat)
    (same : ∀ e ∈ (weightedIndexLoop half 10 j 0 1).getD [], w e.1=v e.1) :
    sourceGather half w j=sourceGather half v j := by
  unfold sourceGather
  congr 1
  apply List.map_congr_left
  intro e he
  rw [same e he]

theorem gather_twice (x : F) (j : Nat) (hj : j<512) :
    sourceGather (2:F)⁻¹ (sourceGather (2:F)⁻¹ (naturalLineValue x)) j=
      x^2*naturalLineValue x j := by
  have same : ∀ e ∈ (weightedIndexLoop (2:F)⁻¹ 10 j 0 1).getD [],
      sourceGather (2:F)⁻¹ (naturalLineValue x) e.1=x*naturalLineValue x e.1 := by
    intro e he
    obtain ⟨es,hw,hb⟩ := weighted_schedule_bounds (2:F)⁻¹ 512 j schedule512_bounded hj
    have hm : e ∈ es := by simpa only [hw,Option.getD_some] using he
    exact sourceGather_natural x e.1 (hb e hm).1
  rw [gather_congr _ _ (fun r => x*naturalLineValue x r) j same,
    gather_scale,sourceGather_natural x j (by omega)]
  ring

theorem even_weight (x y a b c : F) (j : Nat) (hj : j<512) :
    chordDualEven (2:F)⁻¹ (naturalLineValue x) (fun i => y*naturalLineValue x i) a b c j=
      (a+b*x+c*y)*naturalLineValue x j := by
  rw [chordDualEven,sourceGather_natural x j (by omega)]
  ring

theorem odd_weight (x y a b c : F) (circle : x^2+y^2=1) (j : Nat) (hj : j<512) :
    chordDualOdd (2:F)⁻¹ (naturalLineValue x) (fun i => y*naturalLineValue x i) a b c j=
      ((a+b*x+c*y)*y)*naturalLineValue x j := by
  rw [chordDualOdd,gather_twice x j hj,gather_scale,sourceGather_natural x j (by omega)]
  linear_combination -c*naturalLineValue x j*circle

def inputValue (q : Nat → F) (x y : F) : F :=
  rangeDot 512 (naturalLineValue x) (fun i => q (2*i)) +
    y*rangeDot 512 (naturalLineValue x) (fun i => q (2*i+1))

def outputValue (q : Nat → F) (a b c x y : F) : F :=
  rangeDot 514 (naturalLineValue x)
    (finiteChordEven 512 (sourceEdges (2:F)⁻¹ 512) (sourceEdges (2:F)⁻¹ 513) q a b c) +
  rangeDot 514 (fun i => y*naturalLineValue x i)
    (finiteChordOdd 512 (sourceEdges (2:F)⁻¹ 512) q a b c)

theorem chord_evaluation (q : Nat → F) (a b c x y : F) (circle : x^2+y^2=1) :
    outputValue q a b c x y=(a+b*x+c*y)*inputValue q x y := by
  rw [outputValue,source_chord_lane_pairing]
  have he : rangeDot 512
      (chordDualEven (2:F)⁻¹ (naturalLineValue x) (fun i => y*naturalLineValue x i) a b c)
      (fun i => q (2*i))=(a+b*x+c*y)*rangeDot 512 (naturalLineValue x) (fun i => q (2*i)) := by
    unfold rangeDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [even_weight x y a b c i (Finset.mem_range.mp hi)]
    ring
  have ho : rangeDot 512
      (chordDualOdd (2:F)⁻¹ (naturalLineValue x) (fun i => y*naturalLineValue x i) a b c)
      (fun i => q (2*i+1))=((a+b*x+c*y)*y)*rangeDot 512 (naturalLineValue x) (fun i => q (2*i+1)) := by
    unfold rangeDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [odd_weight x y a b c circle i (Finset.mem_range.mp hi)]
    ring
  rw [he,ho]
  unfold inputValue
  ring

theorem secant_first_zero (q : Nat → F) (x0 y0 x1 y1 : F) (circle : x0^2+y0^2=1) :
    outputValue q (x0*y1-y0*x1) (y0-y1) (x1-x0) x0 y0=0 := by
  rw [chord_evaluation q _ _ _ x0 y0 circle]
  have h : x0*y1-y0*x1+(y0-y1)*x0+(x1-x0)*y0=0 := by ring
  rw [h,zero_mul]

theorem secant_second_zero (q : Nat → F) (x0 y0 x1 y1 : F) (circle : x1^2+y1^2=1) :
    outputValue q (x0*y1-y0*x1) (y0-y1) (x1-x0) x1 y1=0 := by
  rw [chord_evaluation q _ _ _ x1 y1 circle]
  have h : x0*y1-y0*x1+(y0-y1)*x1+(x1-x0)*y1=0 := by ring
  rw [h,zero_mul]

#print axioms gather_scale
#print axioms gather_congr
#print axioms gather_twice
#print axioms even_weight
#print axioms odd_weight
#print axioms chord_evaluation
#print axioms secant_first_zero
#print axioms secant_second_zero
end
end AspisR19.SourceChordEvaluation
