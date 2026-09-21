import AspisV8R17.SourceGatherLoop

/-! Full-width chord pairing before interleaving/truncation. All 514 lane
positions are retained. No high-tail-zero premise on the quotient is used. -/
set_option autoImplicit false
namespace AspisV8R17
open scoped BigOperators
variable {F : Type*} [CommRing F]

def rangeDot (n : ℕ) (w q : ℕ → F) : F := ∑ i ∈ Finset.range n, w i*q i

theorem rangeDot_add_right (n : ℕ) (w q s : ℕ → F) :
    rangeDot n w (fun i => q i+s i) = rangeDot n w q+rangeDot n w s := by
  simp [rangeDot, mul_add, Finset.sum_add_distrib]

theorem rangeDot_sub_right (n : ℕ) (w q s : ℕ → F) :
    rangeDot n w (fun i => q i-s i) = rangeDot n w q-rangeDot n w s := by
  simp [rangeDot, mul_sub, Finset.sum_sub_distrib]

theorem rangeDot_scale_right (n : ℕ) (w q : ℕ → F) (a : F) :
    rangeDot n w (fun i => a*q i) = a*rangeDot n w q := by
  simp [rangeDot, ← Finset.mul_sum, mul_left_comm]

theorem rangeDot_comm (n : ℕ) (w q : ℕ → F) : rangeDot n w q = rangeDot n q w := by
  simp [rangeDot, mul_comm]

theorem rangeDot_zeroExtend (n m : ℕ) (h : n≤m) (w q : ℕ → F) :
    rangeDot m w (zeroExtend n q) = rangeDot n w q := by
  unfold rangeDot
  calc
    (∑ i ∈ Finset.range m, w i*zeroExtend n q i) =
        ∑ i ∈ Finset.range n, w i*zeroExtend n q i := by
      symm
      apply Finset.sum_subset (Finset.range_mono h)
      intro i hi hn
      simp [zeroExtend, Finset.mem_range] at hn ⊢
      simp [hn]
    _ = _ := Finset.sum_congr rfl (fun i hi => by
      simp [zeroExtend, Finset.mem_range.mp hi])

theorem scatter512_dot514 (half : F) (q w : ℕ → F) :
    rangeDot 514 w (scatterValue (sourceEdges half 512) q) =
      rangeDot 512 (sourceGather half w) q := by
  have hz := scatter_zero_above (sourceEdges half 512) 513
    (fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2) q 513 (by omega)
  unfold rangeDot
  rw [show 514=513+1 from rfl, Finset.sum_range_succ, hz, mul_zero, add_zero]
  exact source_scatter_gather_dot half 512 schedule512_bounded q w

def chordDualEven (half : F) (we wo : ℕ → F) (a b c : F) (i : ℕ) : F :=
  a*we i+b*sourceGather half we i+c*wo i

def chordDualOdd (half : F) (we wo : ℕ → F) (a b c : F) (i : ℕ) : F :=
  c*(we i-sourceGather half (sourceGather half we) i)+a*wo i+b*sourceGather half wo i

theorem source_chord_lane_pairing (half : F) (q we wo : ℕ → F) (a b c : F) :
    rangeDot 514 we (finiteChordEven 512 (sourceEdges half 512) (sourceEdges half 513) q a b c) +
      rangeDot 514 wo (finiteChordOdd 512 (sourceEdges half 512) q a b c) =
    rangeDot 512 (chordDualEven half we wo a b c) (fun i => q (2*i)) +
      rangeDot 512 (chordDualOdd half we wo a b c) (fun i => q (2*i+1)) := by
  have hx := fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2
  have hxx := fun e he => (sourceEdges_bounds half 513 schedule513_bounded e he).2
  have double (v w : ℕ → F) :
      rangeDot 514 w (scatterValue (sourceEdges half 513)
        (scatterValue (sourceEdges half 512) v)) =
      rangeDot 512 (sourceGather half (sourceGather half w)) v :=
    source_double_scatter_gather_dot half v w
  unfold finiteChordEven finiteChordOdd
  simp only [
    scatter_zeroExtend_output _ 513 hx, scatter_zeroExtend_output _ 514 hxx,
    rangeDot_add_right, rangeDot_sub_right, rangeDot_scale_right,
    scatter512_dot514, double, rangeDot_zeroExtend 512 514 (by omega),
    rangeDot_zeroExtend 512 512 (by omega)]
  rw [rangeDot_comm 512 (chordDualEven half we wo a b c),
    rangeDot_comm 512 (chordDualOdd half we wo a b c)]
  unfold chordDualEven chordDualOdd
  simp only [rangeDot_add_right,
    rangeDot_sub_right, rangeDot_scale_right]
  rw [rangeDot_comm 512 (fun i => q (2*i)),
    rangeDot_comm 512 (fun i => q (2*i)),
    rangeDot_comm 512 (fun i => q (2*i)),
    rangeDot_comm 512 (fun i => q (2*i+1)),
    rangeDot_comm 512 (fun i => q (2*i+1)),
    rangeDot_comm 512 (fun i => q (2*i+1)),
    rangeDot_comm 512 (fun i => q (2*i+1))]
  ring

#print axioms rangeDot_zeroExtend
#print axioms scatter512_dot514
#print axioms source_chord_lane_pairing
end AspisV8R17
