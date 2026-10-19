import AspisR1BatchedFoldSourceStep
import AspisR1BatchedUsizeFlushBridgePublic

set_option autoImplicit false
open Aeneas.Std

namespace AspisR1BatchedSourceCadence

abbrev Usize := UScalar UScalarTy.Usize

def flushAt (terms : Nat) (hterms : terms < 2 ^ UScalarTy.Usize.numBits) : Bool :=
  decide ((UScalar.and (UScalar.ofNatCore (ty := UScalarTy.Usize) terms hterms) (3#usize)).val = 3)

theorem flushAt_iff_mod4 (terms : Nat) (hterms : terms < 2 ^ UScalarTy.Usize.numBits) :
    flushAt terms hterms = true ↔ terms % 4 = 3 := by
  simp only [flushAt, decide_eq_true_eq]
  have hs := AspisR1BatchedUsizeFlushBridgePublic.source_usize_flush_test_iff
      (UScalar.ofNatCore (ty := UScalarTy.Usize) terms hterms)
  have hv : (UScalar.ofNatCore (ty := UScalarTy.Usize) terms hterms).val = terms := rfl
  rw [hv] at hs
  exact hs

def sourcePushUsize (terms : Nat) (hterms : terms < 2 ^ UScalarTy.Usize.numBits)
    (raw product : Nat) : Nat :=
  if flushAt terms hterms then
    AspisR1BatchedFoldSourceStep.fold (raw + product)
  else raw + product

theorem sourcePushUsize_eq (terms : Nat) (hterms : terms < 2 ^ UScalarTy.Usize.numBits)
    (raw product : Nat) :
    sourcePushUsize terms hterms raw product =
      AspisR1BatchedFoldSourceStep.sourcePush terms raw product := by
  by_cases h : terms % 4 = 3
  · have hb : flushAt terms hterms = true := (flushAt_iff_mod4 terms hterms).2 h
    simp [sourcePushUsize, AspisR1BatchedFoldSourceStep.sourcePush, h, hb]
  · have hb : flushAt terms hterms = false := Bool.eq_false_of_not_eq_true (fun ht => h ((flushAt_iff_mod4 terms hterms).1 ht))
    simp [sourcePushUsize, AspisR1BatchedFoldSourceStep.sourcePush, h, hb]

/-- Four pushes using the source's exact `Usize.and` flush predicate. The only
machine-side premise is that the four counter values are representable. -/
theorem sourceFourPushUsize (terms raw a b c d : Nat)
    (h0 : terms < 2 ^ UScalarTy.Usize.numBits)
    (h1 : terms + 1 < 2 ^ UScalarTy.Usize.numBits)
    (h2 : terms + 2 < 2 ^ UScalarTy.Usize.numBits)
    (h3 : terms + 3 < 2 ^ UScalarTy.Usize.numBits)
    (hboundary : terms % 4 = 0) (hr : raw < 2 ^ 34)
    (ha : a ≤ (2 ^ 31 - 2) ^ 2) (hb : b ≤ (2 ^ 31 - 2) ^ 2)
    (hc : c ≤ (2 ^ 31 - 2) ^ 2) (hd : d ≤ (2 ^ 31 - 2) ^ 2) :
    let r1 := sourcePushUsize terms h0 raw a
    let r2 := sourcePushUsize (terms + 1) h1 r1 b
    let r3 := sourcePushUsize (terms + 2) h2 r2 c
    let r4 := sourcePushUsize (terms + 3) h3 r3 d
    r1 < 2 ^ 64 ∧ r2 < 2 ^ 64 ∧ r3 < 2 ^ 64 ∧
      r4 < 2 ^ 34 ∧
      r4 % AspisR1BatchedFoldSourceStep.modulus =
        (raw + a + b + c + d) % AspisR1BatchedFoldSourceStep.modulus := by
  have hnat := AspisR1BatchedFoldSourceStep.sourceFourPush
    terms raw a b c d hboundary hr ha hb hc hd
  simpa only [sourcePushUsize_eq] using hnat

#print axioms flushAt_iff_mod4
#print axioms sourcePushUsize_eq
#print axioms sourceFourPushUsize

end AspisR1BatchedSourceCadence
