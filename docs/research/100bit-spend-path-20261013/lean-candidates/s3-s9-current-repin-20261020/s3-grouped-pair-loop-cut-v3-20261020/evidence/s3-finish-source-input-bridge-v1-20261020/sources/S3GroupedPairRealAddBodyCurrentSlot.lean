import AspisR1GroupedPairCut.Proofs.S3GroupedPairLoop0BodyBind
import S3GroupedPairRealAddCurrent
import S3GroupedPairFinishInputCanonicalCurrent
import Aeneas.Std.RangeIter

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP

namespace AspisR1GroupedPairCut.Proofs.RealAddCurrent

def CanonicalAccumulatorArray (a : Array field.WideExact 12#usize) : Prop :=
  ∀ j : Fin 12, Canonical (a.val[j.val]'(by
    have hp := a.property
    change a.val.length = 12 at hp
    omega))

/-- One actual loop slot. A successful finish-field decode and its exact
same-slot array binding supply canonicality of the input passed to add. -/
theorem loop0_body_from_finishField
    (mulOp : field.WideExact → field.WideExact → Result field.WideExact)
    (bytes : Slice U8)
    (coeff : Array field.WideExact 64#usize)
    (iter : core.ops.range.Range Std.Usize)
    (coefficients : Array field.WideExact 12#usize)
    (j : Std.Usize) (iterNext : core.ops.range.Range Std.Usize)
    (groupByte : Std.U8) (group : Std.Usize)
    (parsed : AspisR1CurrentWide.Proof.FinishE)
    (hj : j.val < 64) (hgroupBound : group.val < 12)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some j, iterNext))
    (hgroup : Array.index_usize weights.S2_INACTIVE_GROUPS j = .ok groupByte)
    (hcast : lift (UScalar.cast .Usize groupByte) = .ok group)
    (hfield : AspisR1CurrentWide.Proof.finishField bytes j = .ok parsed)
    (hvalue : coeff.val[j.val]'(by
        have hp := coeff.property
        change coeff.val.length = 64 at hp
        omega) =
      AspisR1GroupedPairCut.Proofs.FinishInputCanonicalCurrent.finishToS parsed)
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
  have hgroupIndex : group.val < coefficients.length := by
    simpa [coefficients.property] using hgroupBound
  have hcoeffIndex : j.val < coeff.length := by
    simpa [coeff.property] using hj
  obtain ⟨oldCoeff, hold, holdValue⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec coefficients group hgroupIndex)
  obtain ⟨inputCoeff, hin, hinValue⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec coeff j hcoeffIndex)
  have hOldCanonical : Canonical oldCoeff := by
    rw [holdValue]
    exact haccCanonical ⟨group.val, hgroupBound⟩
  have hInputCanonical : Canonical inputCoeff := by
    rw [hinValue]
    rw [hvalue]
    exact AspisR1GroupedPairCut.Proofs.FinishInputCanonicalCurrent.finishField_s3_canonical
      bytes j parsed hfield
  obtain ⟨newCoeff, hadd, hnewCanonical, haddValue⟩ :=
    add_total_exact oldCoeff inputCoeff hOldCanonical hInputCanonical
  obtain ⟨updated, hupdate, _⟩ :=
    WP.spec_imp_exists (Array.update_spec coefficients group newCoeff hgroupIndex)
  have hbody := grouped_pair_loop0_body_success (ops mulOp) coeff iter coefficients
    j iterNext groupByte group oldCoeff inputCoeff newCoeff updated
    hnext hgroup hcast hold hin hadd hupdate
  exact ⟨oldCoeff, inputCoeff, newCoeff, updated, hold, hin, hadd, hupdate,
    haddValue, hbody⟩

end AspisR1GroupedPairCut.Proofs.RealAddCurrent

#print axioms AspisR1GroupedPairCut.Proofs.RealAddCurrent.loop0_body_from_finishField
