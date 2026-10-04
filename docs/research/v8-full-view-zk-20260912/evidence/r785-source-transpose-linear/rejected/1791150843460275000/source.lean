import AspisV8R17.SourceChordTranspose

/-! Additive and scalar linearity of the finite source gather and transpose. -/
set_option autoImplicit false
namespace AspisV8R19.R785SourceTransposeLinear

open AspisV8R17
noncomputable section

theorem source_gather_linear
    {F : Type*} [CommRing F] (half x y : F) (w v : Nat → F) (i : Nat) :
    sourceGather half (fun j => x * w j + y * v j) i =
      x * sourceGather half w i + y * sourceGather half v i := by
  have hlist : ∀ es : List (Nat × F),
      (es.map (fun e => e.2 * (x * w e.1 + y * v e.1))).sum =
        x * (es.map (fun e => e.2 * w e.1)).sum +
          y * (es.map (fun e => e.2 * v e.1)).sum := by
    intro es
    induction es with
    | nil => simp
    | cons e es ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        ring
  unfold sourceGather
  exact hlist ((weightedIndexLoop half 10 i 0 1).getD [])

theorem source_chord_transpose_linear
    {F : Type*} [CommRing F] (half x y a b c : F) (w v : Nat → F) (i : Nat) :
    sourceChordTranspose half (fun j => x * w j + y * v j) a b c i =
      x * sourceChordTranspose half w a b c i +
        y * sourceChordTranspose half v a b c i := by
  have hzero (n : Nat) (r : Nat) :
      zeroExtend n (fun j => x * w j + y * v j) r =
        x * zeroExtend n w r + y * zeroExtend n v r := by
    unfold zeroExtend
    split <;> simp <;> ring
  unfold sourceChordTranspose interleave
  split
  · simp only [chordDualEven]
    rw [hzero, source_gather_linear, hzero, source_gather_linear]
    ring
  · simp only [chordDualOdd]
    rw [hzero, source_gather_linear, hzero, source_gather_linear,
      source_gather_linear, hzero, source_gather_linear]
    ring

#print axioms source_gather_linear
#print axioms source_chord_transpose_linear

end
end AspisV8R19.R785SourceTransposeLinear
