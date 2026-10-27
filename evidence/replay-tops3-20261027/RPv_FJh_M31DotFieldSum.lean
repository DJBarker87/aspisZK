import RPv_RawPoseidonRowField
import ExtractedMaskQM31Exact
import RPv_FJh_Base
import RPv_FJh_InternalStateWords
import RPv_FJh_InternalAccumulatorModel

set_option autoImplicit false
namespace AspisR1.FJh_M31DotFieldSum

open Aeneas Aeneas.Std
open AspisV8R15.ExactTowerBase
open AspisR1.FJh_Base (QM Exact Decode cell)
open AspisR1.FJh_InternalStateWords (wordVec)
open AspisR1.FJh_InternalAccumulatorModel (wordVec_decode)
open AspisR1.RawPoseidonRowField (decodeWords decodeWords_add decodeWords_nat_mul)

/-- Coordinatewise Nat addition commutes with the exact four-word decoder. -/
theorem decodeWords_list_coordinate_sum (xs : List (Fin 4 → Nat)) :
    decodeWords (fun j => (xs.map (fun row => row j)).sum) =
      (xs.map decodeWords).sum := by
  induction xs with
  | nil =>
      ext <;> simp [AspisR1.RawPoseidonRowField.decodeWords]
  | cons row rows ih =>
      change decodeWords (fun j => row j + (rows.map (fun tail => tail j)).sum) =
        decodeWords row + (rows.map decodeWords).sum
      rw [decodeWords_add, ih]

/-- Decode a pointwise finite sum of coordinate vectors as the sum of their
exact decoded words. This is structural in the list, with no field expansion. -/
theorem decodeWords_ofFn_coordinate_sum
    (N : Nat) (coordinate : Fin N → Fin 4 → Nat) :
    decodeWords (fun j => (List.ofFn (fun i : Fin N => coordinate i j)).sum) =
      (List.ofFn (fun i : Fin N => decodeWords (coordinate i))).sum := by
  have h := decodeWords_list_coordinate_sum
    (List.ofFn (fun i : Fin N => coordinate i))
  simpa only [List.map_ofFn, Function.comp_def] using h

/-- A weighted QM31 word vector decodes to the exact-field scalar multiple
of its decoded QM31 value. -/
theorem decode_wordVec_weighted
    (q : QM) (n : U32) :
    decodeWords (fun j : Fin 4 =>
      (cell (wordVec q) j).val * n.val) = Decode q * (n.val : Exact) := by
  calc
    decodeWords (fun j : Fin 4 => (cell (wordVec q) j).val * n.val) =
        (n.val : Exact) * decodeWords (fun j : Fin 4 => (cell (wordVec q) j).val) := by
          simpa only [Nat.mul_comm] using
            decodeWords_nat_mul n.val (fun j : Fin 4 => (cell (wordVec q) j).val)
    _ = (n.val : Exact) * Decode q := by rw [wordVec_decode]
    _ = Decode q * (n.val : Exact) := by rw [mul_comm]

/-- The root's coordinatewise Nat weighted sum is exactly the ordered sum of
its QM31 words multiplied in the exact field by their unsigned U32 weights. -/
theorem decode_coordinatewise_nat_weighted_sum
    {N : Nat} (w : Fin N → QM) (v : Fin N → U32) :
    decodeWords (fun j : Fin 4 =>
      (List.ofFn (fun i : Fin N =>
        (cell (wordVec (w i)) j).val * (v i).val)).sum) =
      (List.ofFn (fun i : Fin N =>
        Decode (w i) * ((v i).val : Exact))).foldl (· + ·) 0 := by
  have hterms : ∀ i : Fin N,
      decodeWords (fun j : Fin 4 =>
        (cell (wordVec (w i)) j).val * (v i).val) =
        Decode (w i) * ((v i).val : Exact) := by
    intro i
    exact decode_wordVec_weighted (w i) (v i)
  calc
    decodeWords (fun j : Fin 4 =>
      (List.ofFn (fun i : Fin N =>
        (cell (wordVec (w i)) j).val * (v i).val)).sum) =
        (List.ofFn (fun i : Fin N =>
          decodeWords (fun j : Fin 4 =>
            (cell (wordVec (w i)) j).val * (v i).val))).sum :=
      decodeWords_ofFn_coordinate_sum N
        (fun i j => (cell (wordVec (w i)) j).val * (v i).val)
    _ = (List.ofFn (fun i : Fin N =>
          Decode (w i) * ((v i).val : Exact))).sum := by
      have hlists :
          List.ofFn (fun i : Fin N =>
            decodeWords (fun j : Fin 4 =>
              (cell (wordVec (w i)) j).val * (v i).val)) =
          List.ofFn (fun i : Fin N => Decode (w i) * ((v i).val : Exact)) :=
        congrArg List.ofFn (funext hterms)
      exact congrArg List.sum hlists
    _ = (List.ofFn (fun i : Fin N =>
          Decode (w i) * ((v i).val : Exact))).foldl (· + ·) 0 := by
      rw [List.sum_eq_foldl]

#print axioms decodeWords_list_coordinate_sum
#print axioms decodeWords_ofFn_coordinate_sum
#print axioms decode_wordVec_weighted
#print axioms decode_coordinatewise_nat_weighted_sum
end AspisR1.FJh_M31DotFieldSum
