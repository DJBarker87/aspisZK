import R22ControlBounds
import Stage2ContinuationTypes

set_option autoImplicit false
namespace AspisR1.R22Stage2ControlBounds
open Aeneas Aeneas.Std Result

/-- A binary traversal maintains w ≤ i < n ≤ 16. The paired branch
additionally checks i+1<n; it therefore consumes two valid entries. -/
theorem binary_frontier (i n w : Nat) (h : w ≤ i ∧ i < n ∧ n ≤ 16) :
    i < 16 ∧ w < 16 ∧ i+1 ≤ 16 ∧ w+1 ≤ 16 ∧
    (i+1 < n → i+1 < 16 ∧ i+2 ≤ n) := by omega

/-- Range guard for the contiguous parent group in node_count. -/
theorem parent_group (i j n width : Nat)
    (h : i < j ∧ j ≤ n ∧ n ≤ 16 ∧ j-i ≤ width ∧ width ≤ 8) :
    j-i ≤ width ∧ width-(j-i) ≤ 8 ∧ i < 16 ∧ j ≤ 16 := by omega

/-- Count is a budget, not an arbitrary usize accumulator. Even the failing
slice-get branch computes at+32 first, so allow one attempted read. -/
theorem sibling_read (used : Nat) (h : used ≤ 914) :
    32*used ≤ 29248 ∧ 32*used+32 ≤ 29280 ∧ 32*used+32 < 4294967296 := by omega

theorem compact_opening (i : Nat) (h : i < 22) :
    i*832 ≤ 17472 ∧ 10055+i*832 ≤ 27527 ∧
    10055+i*832+832 ≤ 28359 := by omega

theorem compact_nodes (used count : Nat) (h : used+count ≤ 914) :
    32*count ≤ 29248 ∧ 28359+32*used+32*count ≤ 57607 := by omega

/-- These are cursor bounds required by the checkpoint decoder; field
canonicality and node-index bounds alone do not imply them. -/
theorem checkpoint_read (cursor size n : Nat) (h : cursor+n ≤ size ∧ size ≤ 4880) :
    cursor+n ≤ 4880 ∧ cursor ≤ cursor+n ∧ cursor+n < 4294967296 := by omega

theorem query_offsets (q start inverseLength lineLength : Nat)
    (h : start ≤ q ∧ q < 22 ∧ q-start < inverseLength ∧ q-start < lineLength) :
    q < 22 ∧ 4*q+3 ≤ 87 ∧ 2*q+1 ≤ 43 ∧ q+1 ≤ 22 ∧
    q-start < inverseLength ∧ q-start < lineLength := by omega

theorem geometry_layout (q start stop : Nat)
    (h : start ≤ q ∧ q < stop ∧ stop ≤ 22) :
    q-start < stop-start ∧ 5*(q-start)+4 < 5*(stop-start) ∧
    5*(stop-start) ≤ 110 := by omega

theorem basis_indices (width j : Nat) (h : j < width ∧ width ≤ 256) :
    j < 256 ∧ j+1 ≤ 256 ∧ 4*j+3 < 1024 := by omega

theorem finish_indices (width j round : Nat)
    (h : j < width ∧ width ≤ 256 ∧ round < 2) :
    j+1 ≤ 256 ∧ 32*j+32 ≤ 32*width ∧
    3*round ≤ 3 ∧ 3*round+2 ≤ 5 := by omega

/-- Total checked arithmetic, with the machine bound retained explicitly. -/
theorem add_total (a b : Usize) (h : a.val+b.val ≤ Usize.max) :
    ∃ c : Usize, (a+b : Result Usize) = ok c ∧ c.val = a.val+b.val := by
  apply WP.spec_imp_exists
  apply UScalar.add_spec
  simpa only [UScalar.max_USize_eq] using h

theorem mul_total (a b : Usize) (h : a.val*b.val ≤ Usize.max) :
    ∃ c : Usize, (a*b : Result Usize) = ok c ∧ c.val = a.val*b.val := by
  apply WP.spec_imp_exists
  apply UScalar.mul_spec
  simpa only [UScalar.max_USize_eq] using h

/-- Reuse the stage-1 polynomial and byte-index facts for stage-2 children. -/
theorem shared_field_byte_bounds (i byte : Nat) (hi : i < 8) (hb : byte < 4) :
    4*i < 32 ∧ 4*i+byte < 32 ∧ i+1 ≤ 8 :=
  R22ControlBounds.sampler_word_indices i byte hi hb

#print axioms binary_frontier
#print axioms parent_group
#print axioms sibling_read
#print axioms compact_opening
#print axioms compact_nodes
#print axioms checkpoint_read
#print axioms query_offsets
#print axioms geometry_layout
#print axioms basis_indices
#print axioms finish_indices
#print axioms add_total
#print axioms mul_total
#print axioms shared_field_byte_bounds
end AspisR1.R22Stage2ControlBounds
