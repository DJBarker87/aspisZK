import S3ActualGeneratedLoop0Body
import S3ActualFieldOpsComplete
import Aeneas.Std.RangeIter
open Aeneas Aeneas.Std Result ControlFlow WP

namespace AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete

def CanonicalAccumulatorArray (a : Array S 12#usize) : Prop :=
  ∀ k : Fin 12, Canonical (a.val[k.val]'(by
    have hp := a.property
    change a.val.length = 12 at hp
    omega))

theorem generated_loop0_body_with_actual_decode_add
    (bytes : Slice Std.U8)
    (iter : core.ops.range.Range Std.Usize)
    (coefficients : Array S 12#usize)
    (j : Std.Usize) (iterNext : core.ops.range.Range Std.Usize)
    (groupByte : Std.U8) (group : Std.Usize)
    (inputCoeff : S)
    (hj : j.val < 64) (hgroupBound : group.val < 12)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some j, iterNext))
    (hgroup : Array.index_usize weights.S2_INACTIVE_GROUPS j = .ok groupByte)
    (hcast : lift (UScalar.cast .Usize groupByte) = .ok group)
    (hfield : decodeField bytes j = .ok inputCoeff)
    (hacc : CanonicalAccumulatorArray coefficients) :
    ∃ (oldCoeff newCoeff : S) (updated : Array S 12#usize),
      Array.index_usize coefficients group = .ok oldCoeff ∧
      actualOperations.add oldCoeff inputCoeff = .ok newCoeff ∧
      Array.update coefficients group newCoeff = .ok updated ∧
      decode newCoeff = decode oldCoeff + decode inputCoeff ∧
      weights.s2_grouped_inactive_pair_loop0.body actualOperations
        bytes iter coefficients = .ok (.cont (iterNext, updated)) := by
  have hindex : group.val < coefficients.length := by
    simpa [coefficients.property] using hgroupBound
  obtain ⟨oldCoeff, hold, holdValue⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec coefficients group hindex)
  have hOldCanonical : Canonical oldCoeff := by
    rw [holdValue]
    exact hacc ⟨group.val, hgroupBound⟩
  have hInputCanonical := decodeField_success_canonical bytes j inputCoeff hfield
  obtain ⟨newCoeff, hadd, _hnewCanonical, haddValue⟩ :=
    add_total_exact oldCoeff inputCoeff hOldCanonical hInputCanonical
  obtain ⟨updated, hupdate, _⟩ :=
    WP.spec_imp_exists (Array.update_spec coefficients group newCoeff hindex)
  have hbody :=
    generated_loop0_body_success actualOperations bytes iter coefficients
      j iterNext groupByte group oldCoeff inputCoeff newCoeff updated
      hnext hgroup hcast hold hfield hadd hupdate
  exact ⟨oldCoeff, newCoeff, updated, hold, hadd, hupdate, haddValue, hbody⟩

end AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete

#print axioms AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.generated_loop0_body_with_actual_decode_add
