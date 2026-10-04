import AspisV8R17.WeightedScatter
import Mathlib.Tactic
set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisV8R19.R699SourceTopChordBoundary
open AspisV8R17
variable {F : Type*} [CommRing F]

def indexEdges (n : Nat) : List (Nat × Nat × Nat) :=
  (List.range n).flatMap fun j =>
    ((indexLoop 10 j 0).getD []).map fun e => (j,e.1,e.2)

def weightEdge (half : F) (e : Nat × Nat × Nat) : ScatterEdge Nat Nat F :=
  (e.1,e.2.1,half^e.2.2)

theorem sourceEdges_powers (half : F) (n : Nat) :
    sourceEdges half n = (indexEdges n).map (weightEdge half) := by
  unfold sourceEdges indexEdges
  rw [List.map_flatMap]
  congr 1
  funext j
  have hw := weightedIndexLoop_powers half 10 j 0
  simp only [pow_zero] at hw
  rw [hw]
  cases indexLoop 10 j 0 <;> simp [List.map_map,weightEdge]

theorem weight_filter (half : F) (es : List (Nat × Nat × Nat)) (r : Nat) :
    ((es.map (weightEdge half)).filter (fun e => decide (e.2.1 = r))) =
      (es.filter (fun e => decide (e.2.1 = r))).map (weightEdge half) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons,List.filter_cons,weightEdge] at *
    split <;> simp_all [weightEdge]

theorem scatter_filter (es : List (ScatterEdge Nat Nat F)) (q : Nat → F) (r : Nat) :
    scatterValue (es.filter (fun e => decide (e.2.1 = r))) q r =
      scatterValue es q r := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    by_cases h : e.2.1 = r
    · have ih' := ih
      unfold scatterValue at ih'
      simp [scatterValue,h,ih']
    · have hr : r ≠ e.2.1 := Ne.symm h
      simp only [List.filter_cons, h,decide_false,ite_false,scatterValue,
        List.map_cons,if_neg hr,List.sum_cons,zero_add] at *
      exact ih

-- Only index lists are reduced. No field-valued recurrence is evaluated.
theorem index_512_511 :
    (indexEdges 512).filter (fun e => decide (e.2.1=511)) = [(510,511,0)] := by decide

theorem index_513_511 :
    (indexEdges 513).filter (fun e => decide (e.2.1=511)) = [(510,511,0)] := by decide

theorem index_512_510 :
    (indexEdges 512).filter (fun e => decide (e.2.1=510)) =
      [(509,510,1),(511,510,1)] := by decide

theorem scatter_512_511 (half : F) (q : Nat → F) :
    scatterValue (sourceEdges half 512) q 511 = q 510 := by
  rw [← scatter_filter,sourceEdges_powers,weight_filter,index_512_511]
  simp [scatterValue,weightEdge]

theorem scatter_513_511 (half : F) (q : Nat → F) :
    scatterValue (sourceEdges half 513) q 511 = q 510 := by
  rw [← scatter_filter,sourceEdges_powers,weight_filter,index_513_511]
  simp [scatterValue,weightEdge]

theorem scatter_512_510 (half : F) (q : Nat → F) :
    scatterValue (sourceEdges half 512) q 510 = half*(q 509+q 511) := by
  rw [← scatter_filter,sourceEdges_powers,weight_filter,index_512_510]
  simp [scatterValue,weightEdge,mul_add]

#print axioms sourceEdges_powers
#print axioms index_512_511
#print axioms index_513_511
#print axioms index_512_510
#print axioms scatter_512_511
#print axioms scatter_513_511
#print axioms scatter_512_510

theorem chord_top_even (half a c : F) (q : Nat → F) :
    sourceChord half q a 0 c 1022 =
      a*q 1022+c*(q 1023-half*(q 1019+q 1023)) := by
  unfold sourceChord
  rw [finiteChordCoefficient_eq 512 _ _
    (fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2)
    (fun e he => (sourceEdges_bounds half 513 schedule513_bounded e he).2)]
  simp only [chordCoefficient,show 1022%2=0 by rfl,if_pos rfl,
    show 1022/2=511 by rfl,chordEven,zero_mul,add_zero]
  rw [scatter_513_511,scatter_512_510]
  simp [zeroExtend]

theorem chord_preceding_odd (half a c : F) (q : Nat → F) :
    sourceChord half q a 0 c 1019 = c*q 1018+a*q 1019 := by
  unfold sourceChord
  rw [finiteChordCoefficient_eq 512 _ _
    (fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2)
    (fun e he => (sourceEdges_bounds half 513 schedule513_bounded e he).2)]
  simp [chordCoefficient,chordOdd,zeroExtend]

section Field
variable {K : Type*} [Field K]
/-- The extra active boundary row has a symbolic second-order pivot.
This is a source-shaped map identity, not an active-minor or privacy theorem. -/
theorem top_row_pivot (half a c : K) (q : Nat → K)
    (ha : a ≠ 0) (h22 : q 1022=0) (h23 : q 1023=0) :
    sourceChord half q a 0 c 1022 + (c*half/a)*sourceChord half q a 0 c 1019 =
      (c^2*half/a)*q 1018 := by
  rw [chord_top_even,chord_preceding_odd,h22,h23]
  field_simp
  ring
#print axioms top_row_pivot
end Field
#print axioms chord_top_even
#print axioms chord_preceding_odd
end AspisV8R19.R699SourceTopChordBoundary
