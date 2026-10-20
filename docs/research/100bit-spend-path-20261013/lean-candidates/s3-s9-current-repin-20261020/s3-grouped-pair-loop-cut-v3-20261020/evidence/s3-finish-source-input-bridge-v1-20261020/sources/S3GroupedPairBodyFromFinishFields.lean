import S3GroupedPairFinishCoeffArray
import S3GroupedPairRealAddBodyCurrent

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP

namespace AspisR1GroupedPairCut.Proofs.RealAddCurrent

/-- The body step consumes the actual finish-field values at each coefficient
slot. The only parser-to-array boundary is the explicit `hentry` correspondence. -/
theorem loop0_body_from_finish_fields
    (mulOp : field.WideExact → field.WideExact → Result field.WideExact)
    (bytes : Slice U8)
    (coeff : Array field.WideExact 64#usize)
    (fieldIndex : Fin 64 → Usize)
    (iter : core.ops.range.Range Std.Usize)
    (coefficients : Array field.WideExact 12#usize)
    (j : Std.Usize) (iterNext : core.ops.range.Range Std.Usize)
    (groupByte : Std.U8) (group : Std.Usize)
    (hj : j.val < 64) (hgroupBound : group.val < 12)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some j, iterNext))
    (hgroup : Array.index_usize weights.S2_INACTIVE_GROUPS j = .ok groupByte)
    (hcast : lift (UScalar.cast .Usize groupByte) = .ok group)
    (hentry : ∀ k : Fin 64,
      ∃ x : AspisR1CurrentWide.Proof.FinishE,
        AspisR1CurrentWide.Proof.finishField bytes (fieldIndex k) = .ok x ∧
        coeff.val[k.val]'(by
          have hp := coeff.property
          change coeff.val.length = 64 at hp
          omega) =
          AspisR1GroupedPairCut.Proofs.FinishInputCanonicalCurrent.finishToS x)
    (haccCanonical : CanonicalAccumulatorArray coefficients) :
    ∃ (oldCoeff inputCoeff newCoeff : field.WideExact)
      (updated : Array field.WideExact 12#usize),
      Array.index_usize coefficients group = .ok oldCoeff ∧
      Array.index_usize coeff j = .ok inputCoeff ∧
      (ops mulOp).add oldCoeff inputCoeff = .ok newCoeff ∧
      Array.update coefficients group newCoeff = .ok updated ∧
      decode newCoeff = decode oldCoeff + decode inputCoeff ∧
      weights.s2_grouped_inactive_pair_loop0.body (ops mulOp) coeff iter coefficients =
        .ok (.cont (iterNext, updated)) := by
  have hinputCanonical :=
    AspisR1GroupedPairCut.Proofs.FinishCoeffArray.canonicalInputArray_of_finishField
      bytes coeff fieldIndex hentry
  exact loop0_body_with_real_add mulOp coeff iter coefficients j iterNext groupByte group
    hj hgroupBound hnext hgroup hcast hinputCanonical haccCanonical

end AspisR1GroupedPairCut.Proofs.RealAddCurrent

#print axioms AspisR1GroupedPairCut.Proofs.RealAddCurrent.loop0_body_from_finish_fields
