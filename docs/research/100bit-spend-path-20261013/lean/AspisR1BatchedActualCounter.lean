import AspisR1BatchedFoldSourceStep
import AspisR1BatchedUsizeFlushBridgePublic
import ExtractedCurrentReducer

set_option autoImplicit false
open Aeneas.Std

namespace AspisR1BatchedActualCounter

abbrev Usize := UScalar UScalarTy.Usize

def actualSourcePush (terms : Usize) (raw product : Nat) : Nat :=
  if decide ((UScalar.and terms (3#usize)).val = 3) then
    AspisR1BatchedFoldSourceStep.fold (raw + product)
  else raw + product

theorem actualSourcePush_eq (terms : Usize) (raw product : Nat) :
    actualSourcePush terms raw product =
      AspisR1BatchedFoldSourceStep.sourcePush terms.val raw product := by
  by_cases h : terms.val % 4 = 3
  · have hb :=
      (AspisR1BatchedUsizeFlushBridgePublic.source_usize_flush_test_iff terms).2 h
    have hdec : decide ((UScalar.and terms (3#usize)).val = 3) = true := by simp [hb]
    simp [actualSourcePush, AspisR1BatchedFoldSourceStep.sourcePush, h, hdec]
  · have hn : ¬ (UScalar.and terms (3#usize)).val = 3 := by
      intro hb
      exact h
        ((AspisR1BatchedUsizeFlushBridgePublic.source_usize_flush_test_iff terms).1 hb)
    have hdec : decide ((UScalar.and terms (3#usize)).val = 3) = false := by simp [hn]
    simp [actualSourcePush, AspisR1BatchedFoldSourceStep.sourcePush, h, hdec]

theorem checked_add_one_success (terms : Usize)
    (hbound : terms.val + 1 < 2 ^ UScalarTy.Usize.numBits) :
    ∃ next : Usize, UScalar.add terms (1#usize) = .ok next ∧
      next.val = terms.val + 1 := by
  have hone : (1#usize : Usize).val = 1 := rfl
  obtain ⟨next, htry, hval⟩ :=
    AspisR1.ExtractedCurrentReducerOps.tryMk_success
      (ty := UScalarTy.Usize) (n := terms.val + 1) hbound
  refine ⟨next, ?_, ?_⟩
  · simpa [UScalar.add, hone] using htry
  · simpa [hone] using hval

/-- Four consecutive source pushes, including the actual Usize mask test and
checked counter increments. Every raw prefix fits u64; after the fourth push,
the Mersenne fold restores the group-boundary bound and preserves its residue. -/
theorem actual_four_push (terms : Usize) (raw a b c d : Nat)
    (hcounter : terms.val + 3 < 2 ^ UScalarTy.Usize.numBits)
    (hboundary : terms.val % 4 = 0) (hr : raw < 2 ^ 34)
    (ha : a ≤ (2 ^ 31 - 2) ^ 2) (hb : b ≤ (2 ^ 31 - 2) ^ 2)
    (hc : c ≤ (2 ^ 31 - 2) ^ 2) (hd : d ≤ (2 ^ 31 - 2) ^ 2) :
    ∃ terms1 terms2 terms3 : Usize,
      UScalar.add terms (1#usize) = .ok terms1 ∧ terms1.val = terms.val + 1 ∧
      UScalar.add terms1 (1#usize) = .ok terms2 ∧ terms2.val = terms.val + 2 ∧
      UScalar.add terms2 (1#usize) = .ok terms3 ∧ terms3.val = terms.val + 3 ∧
      let r1 := actualSourcePush terms raw a
      let r2 := actualSourcePush terms1 r1 b
      let r3 := actualSourcePush terms2 r2 c
      let r4 := actualSourcePush terms3 r3 d
      r1 < 2 ^ 64 ∧ r2 < 2 ^ 64 ∧ r3 < 2 ^ 64 ∧
        r4 < 2 ^ 34 ∧
        r4 % AspisR1BatchedFoldSourceStep.modulus =
          (raw + a + b + c + d) % AspisR1BatchedFoldSourceStep.modulus := by
  have h1 : terms.val + 1 < 2 ^ UScalarTy.Usize.numBits := by omega
  have h2 : terms.val + 2 < 2 ^ UScalarTy.Usize.numBits := by omega
  obtain ⟨terms1, ht1, hv1⟩ := checked_add_one_success terms h1
  have h2' : terms1.val + 1 < 2 ^ UScalarTy.Usize.numBits := by rw [hv1]; omega
  obtain ⟨terms2, ht2, hv2⟩ := checked_add_one_success terms1 h2'
  have h3 : terms.val + 3 < 2 ^ UScalarTy.Usize.numBits := hcounter
  have h3' : terms2.val + 1 < 2 ^ UScalarTy.Usize.numBits := by rw [hv2]; omega
  obtain ⟨terms3, ht3, hv3⟩ := checked_add_one_success terms2 h3'
  have hv2' : terms2.val = terms.val + 2 := by omega
  have hv3' : terms3.val = terms.val + 3 := by omega
  have hnat := AspisR1BatchedFoldSourceStep.sourceFourPush
    terms.val raw a b c d hboundary hr ha hb hc hd
  refine ⟨terms1, terms2, terms3, ht1, hv1, ht2, hv2', ht3, hv3', ?_⟩
  simpa only [actualSourcePush_eq, hv1, hv2', hv3'] using hnat

#print axioms actualSourcePush_eq
#print axioms checked_add_one_success
#print axioms actual_four_push

end AspisR1BatchedActualCounter
