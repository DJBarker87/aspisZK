import AspisR1BatchedActualCounter
import AspisR1BatchedReducerBridge

set_option autoImplicit false
open Aeneas.Std

namespace AspisR1BatchedActualReducerFinish

abbrev Usize := UScalar UScalarTy.Usize

/-- The actual four source pushes followed by the retained extracted
`M31.reduce_u64` return the canonical residue of the original sum. -/
theorem actual_four_push_finish (terms : Usize) (raw a b c d : Nat)
    (hcounter : terms.val + 3 < 2 ^ UScalarTy.Usize.numBits)
    (hboundary : terms.val % 4 = 0) (hr : raw < 2 ^ 34)
    (ha : a ≤ (2 ^ 31 - 2) ^ 2) (hb : b ≤ (2 ^ 31 - 2) ^ 2)
    (hc : c ≤ (2 ^ 31 - 2) ^ 2) (hd : d ≤ (2 ^ 31 - 2) ^ 2) :
    ∃ terms1 terms2 terms3,
      UScalar.add terms (1#usize) = .ok terms1 ∧ terms1.val = terms.val + 1 ∧
      UScalar.add terms1 (1#usize) = .ok terms2 ∧ terms2.val = terms.val + 2 ∧
      UScalar.add terms2 (1#usize) = .ok terms3 ∧ terms3.val = terms.val + 3 ∧
      let r1 := AspisR1BatchedActualCounter.actualSourcePush terms raw a
      let r2 := AspisR1BatchedActualCounter.actualSourcePush terms1 r1 b
      let r3 := AspisR1BatchedActualCounter.actualSourcePush terms2 r2 c
      let r4 := AspisR1BatchedActualCounter.actualSourcePush terms3 r3 d
      ∃ hfinal : r4 < 2 ^ 64, ∃ z,
        AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64
            (UScalar.ofNatCore r4 hfinal) = .ok z ∧
          z.val = (raw + a + b + c + d) % AspisR1BatchedFoldSourceStep.modulus ∧
          z.val < AspisR1BatchedFoldSourceStep.modulus := by
  obtain ⟨terms1, terms2, terms3, ht1, hv1, ht2, hv2, ht3, hv3, hrun⟩ :=
    AspisR1BatchedActualCounter.actual_four_push terms raw a b c d
      hcounter hboundary hr ha hb hc hd
  let r1 := AspisR1BatchedActualCounter.actualSourcePush terms raw a
  let r2 := AspisR1BatchedActualCounter.actualSourcePush terms1 r1 b
  let r3 := AspisR1BatchedActualCounter.actualSourcePush terms2 r2 c
  let r4 := AspisR1BatchedActualCounter.actualSourcePush terms3 r3 d
  rcases hrun with ⟨hraw1, hraw2, hraw3, hraw4, hres⟩
  have hres' : r4 % AspisR1BatchedFoldSourceStep.modulus =
      (raw + a + b + c + d) % AspisR1BatchedFoldSourceStep.modulus := by
    simpa only [r1, r2, r3, r4] using hres
  have hraw4' : r4 < 2 ^ 34 := by simpa only [r1, r2, r3, r4] using hraw4
  have hlt : r4 < 2 ^ 64 := by omega
  obtain ⟨z, hfinish, hz, hzlt⟩ :=
    AspisR1BatchedReducerBridge.actual_finish_mod r4
      (raw + a + b + c + d) hlt hres'
  refine ⟨terms1, terms2, terms3, ht1, hv1, ht2, hv2, ht3, hv3, ?_⟩
  have hz' : z.val = (raw + a + b + c + d) %
      AspisR1BatchedFoldSourceStep.modulus := by
    simpa [AspisR1BatchedFoldSourceStep.modulus, AspisR1BatchedFoldArithmetic.modulus] using hz
  have hzlt' : z.val < AspisR1BatchedFoldSourceStep.modulus := by
    simpa [AspisR1BatchedFoldSourceStep.modulus, AspisR1BatchedFoldArithmetic.modulus] using hzlt
  have hfinish' : AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64
      (UScalar.ofNatCore r4 hlt) = .ok z := hfinish
  refine ⟨hlt, z, ?_⟩
  simpa only [r1, r2, r3, r4] using And.intro hfinish' (And.intro hz' hzlt')

#print axioms actual_four_push_finish

end AspisR1BatchedActualReducerFinish
