import LPl_ExpandResult
open Aeneas Aeneas.Std Result LPl_Kit_Release
set_option autoImplicit false
namespace LPn.Expand

/-- Preserve the observed byte's relation to one32-byte write window while
    compressing the untouched prefix/suffix. No global row enumeration. -/
def coordinate (row j : Nat) : Nat :=
  if j < 32*row then 0 else if j < 32*row+32 then 32+(j-32*row) else 64

/-- The scalar observation checked by LPn_K001 at the interior aligned slot.
    Source and overwritten bytes are arbitrary, with no canonicality test. -/
def localByte (source : Nat → U8) (old : U8) (q : Nat) : U8 :=
  if 32 ≤ q ∧ q < 48 then source (q-32)
  else if 48 ≤ q ∧ q < 64 then 0#u8 else old

theorem coordinate_bound (row j : Nat) : coordinate row j < 96 := by
  unfold coordinate
  split <;> try omega
  split <;> omega

/-- Spatial transport of the native single-window observation. The arbitrary
    row is unbounded; the116-row caller is an immediate specialization. -/
theorem local_global (bs before : List U8) (row j : Nat) :
    localByte (fun lane => bs[16*row+lane]?.getD 0#u8)
      (before[j]?.getD 0#u8) (coordinate row j) = LPl.Expand.step bs before row j := by
  by_cases left : j < 32*row
  · simp [coordinate,left,localByte,LPl.Expand.step,show ¬ 32*row ≤ j by omega]
  · by_cases inside : j < 32*row+32
    · by_cases low : j < 32*row+16
      · have h1 : 32 ≤ 32+(j-32*row) ∧ 32+(j-32*row)<48 := by omega
        simp only [coordinate,if_neg left,if_pos inside,localByte,if_pos h1,
          Nat.add_sub_cancel_left,LPl.Expand.step,if_pos (show 32*row≤j ∧ j<32*row+32 by omega),if_pos low]
      · have h1 : ¬ (32 ≤ 32+(j-32*row) ∧ 32+(j-32*row)<48) := by omega
        have h2 : 48 ≤ 32+(j-32*row) ∧ 32+(j-32*row)<64 := by omega
        simp only [coordinate,if_neg left,if_pos inside,localByte,if_neg h1,if_pos h2,
          LPl.Expand.step,if_pos (show 32*row≤j ∧ j<32*row+32 by omega),if_neg low]
    · simp [coordinate,left,inside,localByte,LPl.Expand.step]

/-- A local native observation for each selected byte gives the inherited
    Write relation on the SAME before/after carrier; no full output equality. -/
theorem write_of_observations (bs before after : List U8) (row : Nat)
    (size : after.length=before.length)
    (observed : ∀ j, j<before.length → after[j]?.getD 0#u8 =
      localByte (fun lane => bs[16*row+lane]?.getD 0#u8)
        (before[j]?.getD 0#u8) (coordinate row j)) :
    LPl.Expand.Write bs before after row := by
  refine ⟨size,?_⟩
  intro j hj
  exact (observed j hj).trans (local_global bs before row j)

theorem windows_disjoint (row other j : Nat) (different : row≠other)
    (lo : 32*row≤j) (hi : j<32*row+32) :
    j<32*other ∨ 32*other+32≤j := by omega

/-- K012's chunks_exact_mut offsets and exhaustion imply coverage for every
    valid caller size, including empty and the maximal116-row size. -/
theorem iterator_partition (n row lane : Nat) (bound : n≤1856)
    (aligned : n%16=0) (reached : row<n/16) (within : lane<32) :
    row<116 ∧ 32*row+lane<2*n ∧ 16*row+lane/2<n ∧
      32*(n/16)=2*n := by omega

#print axioms coordinate_bound
#print axioms local_global
#print axioms write_of_observations
#print axioms windows_disjoint
#print axioms iterator_partition
end LPn.Expand
