import AspisV8R19.R743JointSparseEntryBinding
import AspisV8R19.R777GatherConstantOnTargets
import AspisV8R19.R779FixedPoint1LowKernel
import AspisV8R19.R780Point02WeightPrototype
import AspisV8R19.Point1GuardedChunk06
import AspisV8R19.T163SourceTable
import AspisV8R19.TwoSwapSourceTable
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisV8R19.R865PointWeightBlock
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R777GatherConstantOnTargets
open AspisV8R19.R774WeightedScheduleMass
open scoped BigOperators
noncomputable section

abbrev M := ZMod 2147483647
abbrev half : M := 1073741824

def sourceW (point : Fin 10 → M) (n : Nat) : M :=
  extendFin1024 (transportDual inactive 1023 order
    (fun j => sourcePointBasis point j.val)) n
def pw (point : Fin 10 → M) : Nat → M := pointWeight half 7 5 (-5) point
def we (point : Fin 10 → M) : Nat → M := zeroExtend 512 (fun i => sourceW point (2*i))
def wo (point : Fin 10 → M) : Nat → M := zeroExtend 512 (fun i => sourceW point (2*i+1))

def stencilPositions : List Nat := [0,1,2,3,4,5,6,384,385,386,387,388,389,390]

private theorem half_add_half : half + half = (1:M) := by norm_num [half] <;> decide

private theorem targets_0 : indexTargets 0 = [1] := by rfl
private theorem targets_1 : indexTargets 1 = [0,2] := by rfl
private theorem targets_2 : indexTargets 2 = [3] := by rfl
private theorem targets_192 : indexTargets 192 = [193] := by rfl
private theorem targets_193 : indexTargets 193 = [192,194] := by rfl
private theorem targets_194 : indexTargets 194 = [195] := by rfl

private theorem gather_const_0 (point : Fin 10 → M) (C : M)
    (hw : ∀ n, n ∈ stencilPositions → sourceW point n = C) :
    sourceGather half (we point) 0 = C := by
  apply source_gather_constant_on_targets half half_add_half 0 (by decide) (we point) C
  intro r hr
  rw [targets_0] at hr
  simp at hr
  subst r
  exact hw 2 (by decide)

private theorem gather_const_1 (point : Fin 10 → M) (C : M)
    (hw : ∀ n, n ∈ stencilPositions → sourceW point n = C) :
    sourceGather half (we point) 1 = C := by
  apply source_gather_constant_on_targets half half_add_half 1 (by decide) (we point) C
  intro r hr
  rw [targets_1] at hr
  simp at hr
  rcases hr with h | h
  · subst r; exact hw 0 (by decide)
  · subst r; exact hw 4 (by decide)

private theorem gather_const_192 (point : Fin 10 → M) (C : M)
    (hw : ∀ n, n ∈ stencilPositions → sourceW point n = C) :
    sourceGather half (we point) 192 = C := by
  apply source_gather_constant_on_targets half half_add_half 192 (by decide) (we point) C
  intro r hr
  rw [targets_192] at hr
  simp at hr
  subst r
  exact hw 386 (by decide)

private theorem gather_const_193 (point : Fin 10 → M) (C : M)
    (hw : ∀ n, n ∈ stencilPositions → sourceW point n = C) :
    sourceGather half (we point) 193 = C := by
  apply source_gather_constant_on_targets half half_add_half 193 (by decide) (we point) C
  intro r hr
  rw [targets_193] at hr
  simp at hr
  rcases hr with h | h
  · subst r; exact hw 384 (by decide)
  · subst r; exact hw 388 (by decide)

private theorem gather_odd_0 (point : Fin 10 → M) (C : M)
    (hw : ∀ n, n ∈ stencilPositions → sourceW point n = C) :
    sourceGather half (wo point) 0 = C := by
  apply source_gather_constant_on_targets half half_add_half 0 (by decide) (wo point) C
  intro r hr
  rw [targets_0] at hr
  simp at hr
  subst r
  exact hw 3 (by decide)

private theorem gather_odd_1 (point : Fin 10 → M) (C : M)
    (hw : ∀ n, n ∈ stencilPositions → sourceW point n = C) :
    sourceGather half (wo point) 1 = C := by
  apply source_gather_constant_on_targets half half_add_half 1 (by decide) (wo point) C
  intro r hr
  rw [targets_1] at hr
  simp at hr
  rcases hr with h | h
  · subst r; exact hw 1 (by decide)
  · subst r; exact hw 5 (by decide)

private theorem gather_odd_192 (point : Fin 10 → M) (C : M)
    (hw : ∀ n, n ∈ stencilPositions → sourceW point n = C) :
    sourceGather half (wo point) 192 = C := by
  apply source_gather_constant_on_targets half half_add_half 192 (by decide) (wo point) C
  intro r hr
  rw [targets_192] at hr
  simp at hr
  subst r
  exact hw 387 (by decide)

private theorem gather_odd_193 (point : Fin 10 → M) (C : M)
    (hw : ∀ n, n ∈ stencilPositions → sourceW point n = C) :
    sourceGather half (wo point) 193 = C := by
  apply source_gather_constant_on_targets half half_add_half 193 (by decide) (wo point) C
  intro r hr
  rw [targets_193] at hr
  simp at hr
  rcases hr with h | h
  · subst r; exact hw 385 (by decide)
  · subst r; exact hw 389 (by decide)

private theorem double_const_0 (point : Fin 10 → M) (C : M)
    (hw : ∀ n, n ∈ stencilPositions → sourceW point n = C) :
    sourceGather half (sourceGather half (we point)) 0 = C := by
  apply source_gather_double_constant_on_targets half half_add_half 0 (by decide)
    (we point) C
  · intro r hr
    rw [targets_0] at hr
    simp at hr
    subst r
    decide
  · intro r hr
    rcases List.mem_flatMap.mp hr with ⟨j,hj,hi⟩
    rw [targets_0] at hj
    simp at hj
    subst j
    rw [targets_1] at hi
    simp at hi
    rcases hi with hi | hi
    · subst r; exact hw 0 (by decide)
    · subst r; exact hw 4 (by decide)

private theorem double_const_1 (point : Fin 10 → M) (C : M)
    (hw : ∀ n, n ∈ stencilPositions → sourceW point n = C) :
    sourceGather half (sourceGather half (we point)) 1 = C := by
  apply source_gather_double_constant_on_targets half half_add_half 1 (by decide)
    (we point) C
  · intro r hr
    rw [targets_1] at hr
    simp at hr
    rcases hr with h | h
    · subst r; decide
    · subst r; decide
  · intro r hr
    rcases List.mem_flatMap.mp hr with ⟨j,hj,hi⟩
    rw [targets_1] at hj
    simp at hj
    rcases hj with hj | hj
    · subst j
      rw [targets_0] at hi
      simp at hi
      subst r; exact hw 2 (by decide)
    · subst j
      rw [targets_2] at hi
      simp at hi
      subst r; exact hw 6 (by decide)

private theorem double_const_192 (point : Fin 10 → M) (C : M)
    (hw : ∀ n, n ∈ stencilPositions → sourceW point n = C) :
    sourceGather half (sourceGather half (we point)) 192 = C := by
  apply source_gather_double_constant_on_targets half half_add_half 192 (by decide)
    (we point) C
  · intro r hr
    rw [targets_192] at hr
    simp at hr
    subst r; decide
  · intro r hr
    rcases List.mem_flatMap.mp hr with ⟨j,hj,hi⟩
    rw [targets_192] at hj
    simp at hj
    subst j
    rw [targets_193] at hi
    simp at hi
    rcases hi with hi | hi
    · subst r; exact hw 384 (by decide)
    · subst r; exact hw 388 (by decide)

private theorem double_const_193 (point : Fin 10 → M) (C : M)
    (hw : ∀ n, n ∈ stencilPositions → sourceW point n = C) :
    sourceGather half (sourceGather half (we point)) 193 = C := by
  apply source_gather_double_constant_on_targets half half_add_half 193 (by decide)
    (we point) C
  · intro r hr
    rw [targets_193] at hr
    simp at hr
    rcases hr with h | h
    · subst r; decide
    · subst r; decide
  · intro r hr
    rcases List.mem_flatMap.mp hr with ⟨j,hj,hi⟩
    rw [targets_193] at hj
    simp at hj
    rcases hj with hj | hj
    · subst j
      rw [targets_192] at hi
      simp at hi
      subst r; exact hw 386 (by decide)
    · subst j
      rw [targets_194] at hi
      simp at hi
      subst r; exact hw 390 (by decide)

private theorem pw_even_formula (point : Fin 10 → M) (i : Nat) (hi : i < 512) :
    pw point (2*i) = 7*we point i + 5*sourceGather half (we point) i - 5*wo point i := by
  unfold pw pointWeight
  change AspisV8R17.interleave
    (AspisV8R17.chordDualEven half (we point) (wo point) 7 5 (-5))
    (AspisV8R17.chordDualOdd half (we point) (wo point) 7 5 (-5)) (2*i) = _
  rw [AspisV8R17.interleave_even]
  simp [AspisV8R17.chordDualEven]
  ring

private theorem pw_odd_formula (point : Fin 10 → M) (i : Nat) (hi : i < 512) :
    pw point (2*i+1) =
      -5*(we point i-sourceGather half (sourceGather half (we point)) i) +
        7*wo point i + 5*sourceGather half (wo point) i := by
  unfold pw pointWeight
  change AspisV8R17.interleave
    (AspisV8R17.chordDualEven half (we point) (wo point) 7 5 (-5))
    (AspisV8R17.chordDualOdd half (we point) (wo point) 7 5 (-5)) (2*i+1) = _
  rw [AspisV8R17.interleave_odd]
  simp [AspisV8R17.chordDualOdd]

def point0 : Fin 10 → M := AspisR19.SourceStatementPoints.points
  (AspisR19.R750WitnessPointSupport.zFin10 (F := M)) 0
abbrev point1 : Fin 10 → M := AspisV8R19.R748JointWitnessPointEntry.point
def point2 : Fin 10 → M := AspisR19.SourceStatementPoints.points
  (AspisR19.R750WitnessPointSupport.zFin10 (F := M)) 2

private theorem p0_sourceW_zero (n : Nat) (hn : n < 1024)
    (hbit : (((order (⟨n, hn⟩ : Fin 1024)).val >>> 9) &&& 1) = 0) :
    sourceW point0 n = 0 := by
  unfold sourceW extendFin1024
  rw [dif_pos hn]
  have ht := AspisV8R19.R771Point02Transport.point0_transport_exact (F := M)
    (⟨n, hn⟩ : Fin 1024)
  change transportDual inactive 1023 order
    (fun j => sourcePointBasis point0 j.val) ⟨n, hn⟩ = _ at ht
  rw [ht]
  exact AspisR19.R750WitnessPointSupport.source_basis_zero_of_bits (F := M)
    (order (⟨n, hn⟩ : Fin 1024)).val (Or.inl hbit)

private theorem p2_sourceW_zero (n : Nat) (hn : n < 1024)
    (hbit : (((order (⟨n, hn⟩ : Fin 1024)).val >>> 9) &&& 1) = 0) :
    sourceW point2 n = 0 := by
  unfold sourceW extendFin1024
  rw [dif_pos hn]
  have ht := AspisV8R19.R771Point02Transport.point2_transport_exact (F := M)
    (⟨n, hn⟩ : Fin 1024)
  change transportDual inactive 1023 order
    (fun j => sourcePointBasis point2 j.val) ⟨n, hn⟩ = _ at ht
  rw [ht]
  exact AspisR19.R752SharedWitnessPointSupport.point2_source_basis_zero (F := M)
    (order (⟨n, hn⟩ : Fin 1024)).val (Or.inl hbit)

private theorem p1_sourceW_576 (n : Nat) (hn : n < 1024)
    (hbits : (((order (⟨n, hn⟩ : Fin 1024)).val >>> 9) &&& 1) = 0 ∨
      (((order (⟨n, hn⟩ : Fin 1024)).val >>> 8) &&& 1) = 0)
    (hmem : order (⟨n, hn⟩ : Fin 1024) ∈ inactive.erase (1023 : Fin 1024)) :
    sourceW point1 n = 576 := by
  change AspisV8R19.R748JointWitnessPointEntry.w n = 576
  have hw := AspisR19.R754Point1GuardedTransport.w_guarded
    (⟨n, hn⟩ : Fin 1024) hbits
  simpa [hmem, AspisV8R19.R748JointWitnessPointEntry.w] using hw

private theorem p0_stencil_constant (n : Nat) (hn : n ∈ stencilPositions) :
    sourceW point0 n = 0 := by
  simp [stencilPositions] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact p0_sourceW_zero _ (by decide) (by decide)

private theorem p2_stencil_constant (n : Nat) (hn : n ∈ stencilPositions) :
    sourceW point2 n = 0 := by
  simp [stencilPositions] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact p2_sourceW_zero _ (by decide) (by decide)

private theorem p1_stencil_constant (n : Nat) (hn : n ∈ stencilPositions) :
    sourceW point1 n = 576 := by
  simp [stencilPositions] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | exact p1_sourceW_576 _ (by decide) (Or.inl (by decide)) (by decide)
    | exact p1_sourceW_576 _ (by decide) (Or.inr (by decide)) (by decide)

private theorem pw_block_from_stencil (point : Fin 10 → M) (C : M)
    (hw : ∀ n, n ∈ stencilPositions → sourceW point n = C) :
    ∀ t : Fin 4, pw point (384 + t.val) = pw point t.val := by
  intro t
  fin_cases t
  · have h0 := pw_even_formula point 0 (by decide)
    have h192 := pw_even_formula point 192 (by decide)
    rw [h0, h192]
    simp only [we, wo, zeroExtend, sourceW]
    rw [gather_const_0 point C hw, gather_const_192 point C hw]
    have h2 : sourceW point 2 = C := hw 2 (by decide)
    have h386 : sourceW point 386 = C := hw 386 (by decide)
    rw [h2, h386]
    ring
  · have h1 := pw_odd_formula point 0 (by decide)
    have h193 := pw_odd_formula point 192 (by decide)
    rw [h1, h193]
    simp only [we, wo, zeroExtend, sourceW]
    rw [gather_const_0 point C hw, gather_const_192 point C hw,
      gather_odd_0 point C hw, gather_odd_192 point C hw]
    have h2 : sourceW point 2 = C := hw 2 (by decide)
    have h3 : sourceW point 3 = C := hw 3 (by decide)
    have h386 : sourceW point 386 = C := hw 386 (by decide)
    have h387 : sourceW point 387 = C := hw 387 (by decide)
    rw [h2, h3, h386, h387]
    ring
  · have h1 := pw_even_formula point 1 (by decide)
    have h193 := pw_even_formula point 193 (by decide)
    rw [h1, h193]
    simp only [we, wo, zeroExtend, sourceW]
    rw [gather_const_1 point C hw, gather_const_193 point C hw]
    have h4 : sourceW point 4 = C := hw 4 (by decide)
    have h388 : sourceW point 388 = C := hw 388 (by decide)
    rw [h4, h388]
    ring
  · have h1 := pw_odd_formula point 1 (by decide)
    have h193 := pw_odd_formula point 193 (by decide)
    rw [h1, h193]
    simp only [we, wo, zeroExtend, sourceW]
    rw [gather_const_1 point C hw, gather_const_193 point C hw,
      gather_odd_1 point C hw, gather_odd_193 point C hw]
    have h4 : sourceW point 4 = C := hw 4 (by decide)
    have h5 : sourceW point 5 = C := hw 5 (by decide)
    have h388 : sourceW point 388 = C := hw 388 (by decide)
    have h389 : sourceW point 389 = C := hw 389 (by decide)
    rw [h4, h5, h388, h389]
    ring

theorem all_three_point_weight_blocks :
    ∀ p : Fin 3, ∀ t : Fin 4,
      pw (AspisR19.SourceStatementPoints.points
        (AspisV8R19.R750WitnessPointSupport.zFin10 (F := M)) p)
        (384 + t.val) =
      pw (AspisR19.SourceStatementPoints.points
        (AspisV8R19.R750WitnessPointSupport.zFin10 (F := M)) p)
        t.val := by
  intro p t
  fin_cases p
  · exact pw_block_from_stencil point0 0 p0_stencil_constant t
  · change pw point1 (384 + t.val) = pw point1 t.val
    exact pw_block_from_stencil point1 576 p1_stencil_constant t
  · exact pw_block_from_stencil point2 0 p2_stencil_constant t

#print axioms all_three_point_weight_blocks

-- The next theorem will assemble pointWeight values after the transported
-- source weights have been proved constant on stencilPositions.
#check pw_even_formula
#check pw_odd_formula
#print axioms pw_even_formula
#print axioms pw_odd_formula
end
end AspisV8R19.R865PointWeightBlock
