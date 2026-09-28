import V7CallerCurrentReleaseR26Qm31DotRawArithmetic

/-!
# Fixed three-pair iterator used by the current QM31 dot product

The raw Karatsuba accumulator enumerates a literal three-element array.  These
small transition lemmas keep that control flow symbolic instead of unfolding
the complete dot product.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26Qm31DotInnerIterator

abbrev CM31 := field.CM31
abbrev Pair := CM31 × CM31
abbrev PairIterator := core.array.iter.IntoIter Pair 3#usize
abbrev EnumeratedPairIterator :=
  core.iter.adapters.enumerate.Enumerate PairIterator

local instance : Inhabited CM31 :=
  ⟨{ a := field.M31.ZERO, b := field.M31.ZERO }⟩

def usizeOfNatTruncate (value : Nat) : Std.Usize :=
  UScalar.ofNatCore (value % (2 ^ UScalarTy.Usize.numBits)) (by
    exact Nat.mod_lt _ (by positivity))

theorem usizeOfNatTruncate_val_eq {value : Nat}
    (bound : value < UScalar.size .Usize) :
    (usizeOfNatTruncate value).val = value := by
  simp only [usizeOfNatTruncate, UScalar.ofNatCore_val_eq]
  apply Nat.mod_eq_of_lt
  simpa [UScalar.size_def] using bound

def expectedPairIterator (pairs : Array Pair 3#usize) (processed : Nat) :
    EnumeratedPairIterator :=
  { iter := { array := pairs, index := processed, backIndex := 3 },
    count := usizeOfNatTruncate processed }

private theorem small_fits_usize {value : Nat} (bound : value ≤ 4) :
    value < UScalar.size .Usize := by
  have literalBound := UScalar.hSize (5#usize)
  rw [UScalar.size_UScalarTyUsize] at literalBound ⊢
  norm_num at literalBound
  omega

private theorem usize_add_one_ok
    (current next : Std.Usize)
    (valueExact : current.val + 1 = next.val)
    (bound : current.val + 1 < 2 ^ System.Platform.numBits) :
    current + 1#usize = (ok next : Result Std.Usize) := by
  have addSpec := @UScalar.add_equiv UScalarTy.Usize current 1#usize
  generalize runEq : (current + 1#usize) = result at addSpec ⊢
  cases result with
  | fail error =>
      exfalso
      apply addSpec
      simpa using bound
  | div => exact False.elim addSpec
  | ok value =>
      have sameValue : value.val = next.val := by
        calc
          value.val = current.val + (1#usize).val := addSpec.2.1
          _ = current.val + 1 := by rfl
          _ = next.val := valueExact
      have : value = next := UScalar.val_eq_imp value next sameValue
      simp [this]

theorem expected_pair_iterator_next
    (pairs : Array Pair 3#usize) (processed : Nat)
    (active : processed < 3) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator Pair
          3#usize)
        (expectedPairIterator pairs processed) =
      ok (some (usizeOfNatTruncate processed, pairs.val[processed]!),
        expectedPairIterator pairs (processed + 1)) := by
  have listBound : processed < pairs.val.length := by
    have lengthExact : pairs.val.length = 3 := by
      simpa [Array.length_eq] using pairs.property
    omega
  have getExact : pairs.val[processed] = pairs.val[processed]! := by
    symm
    apply List.getElem!_of_getElem?
    simpa using listBound
  have processedFits : processed < UScalar.size .Usize :=
    small_fits_usize (by omega)
  have nextFits : processed + 1 < UScalar.size .Usize :=
    small_fits_usize (by omega)
  have processedVal : (usizeOfNatTruncate processed).val = processed :=
    usizeOfNatTruncate_val_eq processedFits
  have nextVal : (usizeOfNatTruncate (processed + 1)).val = processed + 1 :=
    usizeOfNatTruncate_val_eq nextFits
  have countBound :
      (usizeOfNatTruncate processed).val + 1 <
        2 ^ System.Platform.numBits := by
    rw [processedVal]
    simpa [UScalar.size_def, UScalarTy.Usize_numBits_eq] using nextFits
  have countRun :
      usizeOfNatTruncate processed + 1#usize =
        (ok (usizeOfNatTruncate (processed + 1)) : Result Std.Usize) := by
    apply usize_add_one_ok
    · rw [processedVal, nextVal]
    · exact countBound
  /- Keep the pure wrapping fact available to the later raw-loop proof. -/
  have _countNext :
      Std.Usize.wrapping_add (usizeOfNatTruncate processed) 1#usize =
        usizeOfNatTruncate (processed + 1) := by
    apply UScalar.eq_of_val_eq
    rw [Std.Usize.wrapping_add_val_eq,
      usizeOfNatTruncate_val_eq processedFits,
      usizeOfNatTruncate_val_eq nextFits]
    norm_num
    apply Nat.mod_eq_of_lt
    rw [UScalar.size_UScalarTyUsize] at nextFits
    exact nextFits
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
  simp only [core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator]
  unfold core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
    expectedPairIterator
  rw [dif_pos ⟨active, listBound⟩]
  simp only [bind_tc_ok]
  rw [countRun]
  simp [getExact]

theorem expected_pair_iterator_done (pairs : Array Pair 3#usize) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator Pair
          3#usize)
        (expectedPairIterator pairs 3) =
      ok (none, expectedPairIterator pairs 3) := by
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
  simp [core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    expectedPairIterator]

theorem generated_pair_iterator_initial
    (pairs : Array Pair 3#usize) :
    (do
      let into ←
        Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter pairs
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator Pair
          3#usize) into) =
      ok (expectedPairIterator pairs 0) := by
  simp [Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default,
    expectedPairIterator, usizeOfNatTruncate]

#print axioms expected_pair_iterator_next
#print axioms expected_pair_iterator_done
#print axioms generated_pair_iterator_initial

end V7CallerCurrentReleaseR26Qm31DotInnerIterator
