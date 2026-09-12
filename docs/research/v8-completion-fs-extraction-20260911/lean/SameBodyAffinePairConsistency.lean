import SameBodySourceTerminalWeight
import Mathlib.Tactic.Ring

/-!
# Optimized affine-pair consistency

The source computes ordinary covector entries 0 and 2/1 through one shared
eight/nine-coordinate product.  This leaf proves that optimization equals the
literal full ten-coordinate tensor loop.  Specialisation to the prepared
source record and dense `originalWeight` remains explicit below.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
set_option maxRecDepth 4096

namespace AspisV8Completion.SameBodyAffinePairConsistency

open SameBodySourceRelationProducer SameBodySourceTerminalWeight
open SameBodyLiveRelationObservation SameBodyAuthenticatedIncrement
open SameBodyOrdinary SameBodyPublicCorrection
open AspisPool.V7MerkleQueryGrammar

abbrev K := SameBodySourceRelationProducer.K

noncomputable section

/-- Algebra-only spelling of the full entry loop.  Keeping the already
constructed point table abstract prevents expansion of the successor circuit. -/
def tensorEntry (point : Fin 3 → Fin 10 → K) (scale : Fin 3 → K)
    (index : Fin 3) : K :=
  (List.finRange 3).foldl (fun out row =>
    let value := (List.finRange 10).foldl (fun product coordinate =>
      product * (if index.val / 2 ^ (9 - coordinate.val) % 2 = 0
        then 1 - point row coordinate else point row coordinate)) (scale row)
    out + value) 1

/-- Algebra-only spelling of the optimized entry-pair loop. -/
def tensorPair (point : Fin 3 → Fin 10 → K) (scale : Fin 3 → K)
    (useX : Bool) : K × K :=
  let target : Fin 10 := if useX then 8 else 9
  (List.finRange 3).foldl (fun total row =>
    let common := (List.finRange 10).foldl (fun product coordinate =>
      if coordinate = target then product
      else product * (1 - point row coordinate)) (scale row)
    let right := common * point row target
    (total.1 + (common - right), total.2 + right)) (1, 1)

private def rowEntry (point : Fin 10 → K) (scale : K) (index : Fin 3) : K :=
  (List.finRange 10).foldl (fun product coordinate =>
    product * (if index.val / 2 ^ (9 - coordinate.val) % 2 = 0
      then 1 - point coordinate else point coordinate)) scale

private def rowPair (point : Fin 10 → K) (scale : K) (useX : Bool) : K × K :=
  let target : Fin 10 := if useX then 8 else 9
  let common := (List.finRange 10).foldl (fun product coordinate =>
    if coordinate = target then product
    else product * (1 - point coordinate)) scale
  let right := common * point target
  (common - right, right)

private theorem sub_right (c x : K) : c - c * x = c * (1 - x) := by
  rw [mul_sub]
  simp

private theorem swap_last (c x y : K) : c * x * y = c * y * x := by
  ac_rfl

private theorem finRange10_eq : List.finRange 10 =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide

private theorem finRange3_eq : List.finRange 3 = [0, 1, 2] := by decide

/-- One-row factorization.  This is the only place where the ten tensor
coordinates are expanded; it avoids normalizing the full three-row fold. -/
private theorem rowPair_eq (point : Fin 10 → K) (scale : K) (useX : Bool) :
    rowPair point scale useX =
      (rowEntry point scale 0,
        rowEntry point scale (if useX then 2 else 1)) := by
  cases useX
  · unfold rowPair rowEntry
    rw [finRange10_eq]
    dsimp
    let c := scale * (1 - point 0) * (1 - point 1) * (1 - point 2) *
      (1 - point 3) * (1 - point 4) * (1 - point 5) * (1 - point 6) *
      (1 - point 7) * (1 - point 8)
    apply Prod.ext
    · change c - c * point 9 = c * (1 - point 9)
      exact sub_right c (point 9)
    · rfl
  · unfold rowPair rowEntry
    rw [finRange10_eq]
    dsimp
    apply Prod.ext
    · let c := scale * (1 - point 0) * (1 - point 1) * (1 - point 2) *
        (1 - point 3) * (1 - point 4) * (1 - point 5) * (1 - point 6) *
        (1 - point 7) * (1 - point 9)
      change c - c * point 8 =
        scale * (1 - point 0) * (1 - point 1) * (1 - point 2) *
          (1 - point 3) * (1 - point 4) * (1 - point 5) * (1 - point 6) *
          (1 - point 7) * (1 - point 8) * (1 - point 9)
      exact (sub_right c (point 8)).trans (swap_last _ _ _)
    · exact swap_last _ _ _

/-- The shared-product optimization computes exactly entries zero and two
(`useX`) or zero and one (`useY`).  This is only a 3×10 symbolic identity. -/
theorem tensorPair_eq_entries (point : Fin 3 → Fin 10 → K)
    (scale : Fin 3 → K) (useX : Bool) :
    tensorPair point scale useX =
      (tensorEntry point scale 0,
        tensorEntry point scale (if useX then 2 else 1)) := by
  change (List.finRange 3).foldl (fun total row =>
      let pair := rowPair (point row) (scale row) useX
      (total.1 + pair.1, total.2 + pair.2)) (1, 1) =
    ((List.finRange 3).foldl
        (fun out row => out + rowEntry (point row) (scale row) 0) 1,
      (List.finRange 3).foldl (fun out row =>
        out + rowEntry (point row) (scale row) (if useX then 2 else 1)) 1)
  rw [finRange3_eq]
  cases useX <;> simp [rowPair_eq]

#print axioms tensorPair_eq_entries

/- The remaining specialization is definitionally the requested source
statement, but unfolding `ordinaryOps`, `pair`, `entry`, and `originalWeight`
currently exhausts the focused 250k-heartbeat budget at `whnf`.  No
mathematical premise is missing: the surviving seam is an elaboration-sized
bridge from these abstract `point`/`scale` parameters to the prepared source
record and its `inactiveCoefficient_small = 1` fact. -/

end
end AspisV8Completion.SameBodyAffinePairConsistency
