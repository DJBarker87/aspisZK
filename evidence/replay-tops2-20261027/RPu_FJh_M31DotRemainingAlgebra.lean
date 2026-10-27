import RPu_FJh_M31DotReads
import RPu_FJh_M31DotFieldSum

/-! Structural sum identities for the scalar dot product. No seven-input
recurrence or finite-field multiplication is normalized. -/
set_option autoImplicit false
namespace AspisR1.FJh_M31DotRemainingAlgebra
open Aeneas Aeneas.Std
open AspisR1.FJh_Base (QM Exact Decode)
open AspisR1.FJh_M31DotReads
open AspisR1.RawPoseidonRowField (decodeWords)

theorem remaining_add (weights : Slice QM) (values : Slice U32)
    (start a b : Nat) (j : Fin 4) :
    remaining weights values start (a+b) j = remaining weights values start a j +
      remaining weights values (start+a) b j := by
  induction a generalizing start with
  | zero => simp only [Nat.zero_add,Nat.add_zero,remaining]
  | succ a ih =>
    rw [Nat.succ_add]
    change term weights values start j + remaining weights values (start+1) (a+b) j =
      (term weights values start j + remaining weights values (start+1) a j) +
        remaining weights values (start+(a+1)) b j
    rw [ih]
    have hshift : start+1+a = start+(a+1) := by omega
    rw [hshift,Nat.add_assoc]

theorem remaining_ofFn (weights : Slice QM) (values : Slice U32)
    (start fuel : Nat) (j : Fin 4) :
    remaining weights values start fuel j =
      (List.ofFn (fun i : Fin fuel => term weights values (start+i.val) j)).sum := by
  induction fuel generalizing start with
  | zero => simp only [remaining,List.ofFn_zero,List.sum_nil]
  | succ fuel ih =>
    rw [remaining,List.ofFn_succ,List.sum_cons,ih]
    apply congrArg (term weights values start j + ·)
    apply congrArg List.sum
    apply congrArg List.ofFn
    funext i
    have hshift : start+1+i.val = start+(i.val+1) := by omega
    simp only [Fin.val_succ,hshift]

theorem decode_remaining (weights : Slice QM) (values : Slice U32) (N : Nat)
    (hw : N ≤ weights.val.length) (hv : N ≤ values.val.length) :
    decodeWords (remaining weights values 0 N) =
      (List.ofFn (fun i : Fin N =>
        Decode (sliceCell weights i.val (Nat.lt_of_lt_of_le i.isLt hw)) *
          ((sliceCell values i.val (Nat.lt_of_lt_of_le i.isLt hv)).val : Exact))).foldl (·+·) 0 := by
  let w : Fin N → QM := fun i => sliceCell weights i.val (Nat.lt_of_lt_of_le i.isLt hw)
  let v : Fin N → U32 := fun i => sliceCell values i.val (Nat.lt_of_lt_of_le i.isLt hv)
  have hterm (i : Fin N) (j : Fin 4) :
      term weights values i.val j =
        (AspisR1.FJh_Base.cell (AspisR1.FJh_InternalStateWords.wordVec (w i)) j).val * (v i).val := by
    unfold term
    rw [List.getElem?_eq_getElem (Nat.lt_of_lt_of_le i.isLt hw),
      List.getElem?_eq_getElem (Nat.lt_of_lt_of_le i.isLt hv)]
    rfl
  have hfun : remaining weights values 0 N = (fun j : Fin 4 =>
      (List.ofFn (fun i : Fin N =>
        (AspisR1.FJh_Base.cell (AspisR1.FJh_InternalStateWords.wordVec (w i)) j).val * (v i).val)).sum) := by
    funext j
    rw [remaining_ofFn]
    apply congrArg List.sum
    apply congrArg List.ofFn
    funext i
    simpa only [Nat.zero_add] using hterm i j
  exact (congrArg decodeWords hfun).trans
    (AspisR1.FJh_M31DotFieldSum.decode_coordinatewise_nat_weighted_sum w v)

#print axioms remaining_add
#print axioms remaining_ofFn
#print axioms decode_remaining
end AspisR1.FJh_M31DotRemainingAlgebra
