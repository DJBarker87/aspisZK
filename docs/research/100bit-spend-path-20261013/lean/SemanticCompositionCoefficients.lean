import SemanticPackedOuterClosed
import TerminalCompositionPolynomial
import ExtractedMaskSemanticBridgeConcrete
import ScheduleFamilyFieldTransport
import PathFamilyFieldTransport
import ValueFamilyFieldTransport
import DigestFamilyFieldTransport
import AssetFamilyFieldTransport
import R0P.SemDecision
import R0P.Occupancy

/-! Bridge the actual six-family semantic_packed output to the 24 coefficients
consumed by composition_parts_loop0.  The source poseidon array and copy seed
remain separate inputs to the combined fold theorem. -/
set_option autoImplicit false
namespace AspisR1.SemanticCompositionCoefficients
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQmPackBase4Semantic
open AspisR1.ValueFamilyFieldTransport

abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Wide := AspisWideTower.WideExact
abbrev QM := field.QM31
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev f := AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
abbrev PackB := AspisR1.ExtractedMaskQmPackBase4Semantic.PackB
abbrev exactPublic := AspisR1.SemanticPublicModel.exactPublic
abbrev exactOpenings := AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector

/-- Exact-field image of the existing four-basis-coordinate expression. -/
def exactPack4 (v : Fin 4 → ExactQM) : ExactQM :=
  v 0 + AspisR1.ExtractedMaskTowerBasisExact.iQM * v 1 +
    AspisR1.ExtractedMaskTowerBasisExact.uQM * v 2 +
      (AspisR1.ExtractedMaskTowerBasisExact.iQM *
        AspisR1.ExtractedMaskTowerBasisExact.uQM) * v 3

def exactScalarLane (public1 : Public) (openings : Openings)
    (point : Array QM 10#usize) (index : Nat) : ExactQM :=
  R0P.SemSource.scalarLaneAt (exactPublic public1) (exactOpenings openings)
    (fun i => pointSelector point i) index

def semanticLane24 (public1 : Public) (openings : Openings)
    (point : Array QM 10#usize) (i : Fin 24) : ExactQM :=
  exactPack4 (fun k => exactScalarLane public1 openings point (4*i.val+k.val))

private theorem list_getD_map {K L : Type} [NonAssocSemiring K] [NonAssocSemiring L]
    (g : K →+* L) (xs : List K) (i : Nat) :
    g (xs.getD i 0) = (xs.map g).getD i 0 := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
      cases i with
      | zero => simp
      | succ n =>
          change g (xs.getD n 0) = (xs.map g).getD n 0
          exact ih n

private theorem map_occupancyLanesLiteral {K L : Type} [Field K] [Field L]
    (g : K →+* L) (input output expected : K) (opened : Fin 16 → K) :
    (R0P.occupancyLanesLiteral input output expected opened).map g =
      R0P.occupancyLanesLiteral (g input) (g output) (g expected)
        (fun i => g (opened i)) := by
  simp [R0P.occupancyLanesLiteral, List.map_ofFn, Function.comp_def,
    map_add, map_sub, map_mul, map_one]

private theorem map_occupancyFamily {K L : Type} [Field K] [Field L]
    (g : K →+* L) (pub : R0P.Public K) (pub' : R0P.Public L)
    (o : R0P.Openings K) (sel : R0P.Sel K)
    (hv : pub'.variant = pub.variant) :
    ((R0P.occupancyFamily (K := K)).residuals pub o sel).map g =
      (R0P.occupancyFamily (K := L)).residuals pub' (mapOpenings g o)
        (fun i => g (sel i)) := by
  change (R0P.occupancyLanesLiteral (sel (63*16+9)) (sel (63*16+10))
      (R0P.occupancyExpected pub.variant) o.z).map g = _
  rw [map_occupancyLanesLiteral]
  have he : g (R0P.occupancyExpected pub.variant) =
      R0P.occupancyExpected pub'.variant := by
    rw [← hv]
    cases pub'.variant <;> simp [R0P.occupancyExpected]
  rw [he]
  rfl

private theorem scalarLane_map (public1 : Public) (openings : Openings)
    (point : Array QM 10#usize) (index : Nat) :
    f (exactScalarLane public1 openings point index) =
      R0P.SemSource.scalarLaneAt
        (AspisR1.SemanticPackedSixFamilies.publicWide public1)
        (mapOpenings f (exactOpenings openings))
        (fun i => f (pointSelector point i)) index := by
  let pe := exactPublic public1
  let pw := AspisR1.SemanticPackedSixFamilies.publicWide public1
  let oe := exactOpenings openings
  let se : R0P.Sel ExactQM := fun i => pointSelector point i
  have hv : pw.variant = pe.variant := rfl
  have ha : pw.assetId = f pe.assetId := rfl
  have hw : pw.withdrawalAmount = pe.withdrawalAmount.map f := rfl
  have hsch := AspisR1.ScheduleFamilyFieldTransport.map_family f pe pw oe se hv
  have hocc := map_occupancyFamily f pe pw oe se hv
  have hpath := AspisR1.PathFamilyFieldTransport.map_family f pe pw oe se
  have hvalue := AspisR1.ValueFamilyFieldTransport.map_family f pe pw oe se
  have hdigest := AspisR1.DigestFamilyFieldTransport.map_family f pe oe se
  have hasset := AspisR1.AssetFamilyFieldTransport.map_family f pe pw oe se hv ha hw
  have hmapPub : AspisR1.SpendDataMap.mapPublic f pe = pw := rfl
  unfold exactScalarLane
  change f (R0P.SemSource.scalarLaneAt pe oe se index) = _
  unfold R0P.SemSource.scalarLaneAt
  by_cases h12 : index < 12
  · simp only [if_pos h12, map_add]
    rw [list_getD_map, hsch, list_getD_map, hocc]
  · simp only [if_neg h12]
    by_cases h32 : index < 32
    · simp only [if_pos h32]
      rw [list_getD_map, hsch]
    · simp only [if_neg h32]
      by_cases h49 : index < 49
      · simp only [if_pos h49]
        rw [list_getD_map, hpath]
      · simp only [if_neg h49]
        by_cases h84 : index < 84
        · simp only [if_pos h84]
          rw [list_getD_map, hvalue]
        · simp only [if_neg h84]
          by_cases h92 : index < 92
          · simp only [if_pos h92]
            rw [list_getD_map, hdigest, hmapPub]
          · simp only [if_neg h92]
            by_cases h94 : index < 94
            · simp only [if_pos h94]
              rw [list_getD_map, hasset]
            · simp only [if_neg h94, map_zero]

private theorem exactPack4_maps (v : Fin 4 → ExactQM) :
    f (exactPack4 v) = R0P.pack4 PackB (fun k => f (v k)) := by
  have hi : f AspisR1.ExtractedMaskQmPackBase4Arithmetic.iBasis = PackB.i := by
    have hbase : AspisR1.ExtractedMaskQmPackBase4Arithmetic.iBasis =
        AspisR1.ExtractedMaskTowerBasisExact.basisElement 1 := rfl
    rw [hbase]
    have h := AspisR1.ExtractedMaskSemanticBridgeConcrete.basisCompatible
      (1 : Fin 4)
    change f (AspisR1.ExtractedMaskTowerBasisExact.basisElement 1) =
      R0P.Mask.towerBasis PackB 1 at h
    simpa [R0P.Mask.towerBasis,
      AspisR1.ExtractedMaskTowerBasisExact.basisElement] using h
  have hu : f AspisR1.ExtractedMaskQmPackBase4Arithmetic.uBasis = PackB.u := by
    have hbase : AspisR1.ExtractedMaskQmPackBase4Arithmetic.uBasis =
        AspisR1.ExtractedMaskTowerBasisExact.basisElement 2 := rfl
    rw [hbase]
    have h := AspisR1.ExtractedMaskSemanticBridgeConcrete.basisCompatible
      (2 : Fin 4)
    change f (AspisR1.ExtractedMaskTowerBasisExact.basisElement 2) =
      R0P.Mask.towerBasis PackB 2 at h
    simpa [R0P.Mask.towerBasis,
      AspisR1.ExtractedMaskTowerBasisExact.basisElement] using h
  change f (v 0 +
    AspisR1.ExtractedMaskQmPackBase4Arithmetic.iBasis * v 1 +
    AspisR1.ExtractedMaskQmPackBase4Arithmetic.uBasis * v 2 +
    (AspisR1.ExtractedMaskQmPackBase4Arithmetic.iBasis *
      AspisR1.ExtractedMaskQmPackBase4Arithmetic.uBasis) * v 3) = _
  simp only [map_add, map_mul, hi, hu, R0P.pack4]

/-- Convert any retained six-family packed equations into exact-field 24-cell
coefficients. This is reusable for arrays supplied by the preparation prelude;
it does not rerun the source loop. -/
theorem coefficients_of_packed_equations
    (semantic : Array QM 24#usize) (point : Array QM 10#usize)
    (public1 : Public) (openings : Openings)
    (hpacked : ∀ i : Fin 24,
      f (AspisR1.PreweightedLoopModel.decoded semantic i) =
        R0P.pack4 PackB (fun k =>
          R0P.SemSource.scalarLaneAt
            (AspisR1.SemanticPackedSixFamilies.publicWide public1)
            (mapOpenings f (exactOpenings openings))
            (fun j => f (pointSelector point j)) (4*i.val+k.val))) :
    ∀ i : Fin 24, AspisR1.PreweightedLoopModel.decoded semantic i =
      semanticLane24 public1 openings point i := by
  intro i
  have hcell := hpacked i
  have hmap : f (semanticLane24 public1 openings point i) =
      R0P.pack4 PackB (fun k => f (exactScalarLane public1 openings point
        (4*i.val+k.val))) := by
    exact exactPack4_maps (fun k => exactScalarLane public1 openings point (4*i.val+k.val))
  have hwide' : f (AspisR1.PreweightedLoopModel.decoded semantic i) =
      R0P.pack4 PackB (fun k => f (exactScalarLane public1 openings point
        (4*i.val+k.val))) := by
    simpa only [exactPublic, exactOpenings, pointSelector, scalarLane_map] using hcell
  exact f.injective (hwide'.trans hmap.symm)

/-- Exact coefficient interpretation of the actual semantic_packed result.
This removes the 24-cell array-to-model premise needed by the Horner fold. -/
theorem actual_semantic_coefficients
    (point : Array QM 10#usize) (selectors : Selectors)
    (public1 : Public) (openings : Openings)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hz : CanonicalArray openings.z) (hsucc : CanonicalArray openings.succ_z)
    (hxor : CanonicalArray openings.xor12_z)
    (ha : AspisR1.DigestFixedPrefix.DigestWordsCanonical public1.anchor)
    (hn : AspisR1.DigestFixedPrefix.DigestWordsCanonical public1.nullifier)
    (hc : AspisR1.DigestFixedPrefix.DigestWordsCanonical public1.change)
    (hr : ∀ recipient, public1.recipient = some recipient → AspisR1.DigestFixedPrefix.DigestWordsCanonical recipient)
    (hsnapshot : ∀ j : Fin 20, AspisR1.DigestFixedPrefix.DigestWordsCanonical
      (public1.transition.live_snapshot.frontier.val[j.val]'(by
        simpa [public1.transition.live_snapshot.frontier.property] using j.isLt)))
    (hroot : AspisR1.DigestFixedPrefix.DigestWordsCanonical public1.transition.candidate_afterstate.next_root)
    (hfrontier : ∀ j : Fin 20, AspisR1.DigestFixedPrefix.DigestWordsCanonical
      (public1.transition.candidate_afterstate.next_frontier.val[j.val]'(by
        simpa [public1.transition.candidate_afterstate.next_frontier.property] using j.isLt)))
    (hasset : public1.asset_id.val < AspisR1.TerminalLiftM31Exact.P)
    (hamount : (AspisR1.ScalarSuffixExecution.amountValue public1).val < AspisR1.TerminalLiftM31Exact.P) :
    ∃ semantic : Array QM 24#usize,
      AspisR1SemanticPackedBoundedCandidate.pool_v1.pair_forest_semantic_terminal.semantic_packed
        public1 openings selectors = .ok semantic ∧ CanonicalArray semantic ∧
      ∀ i : Fin 24, AspisR1.PreweightedLoopModel.decoded semantic i =
        semanticLane24 public1 openings point i := by
  obtain ⟨semantic, hrun, hcan, hwide⟩ :=
    AspisR1.SemanticPackedOuterClosed.actual_semantic_packed point selectors public1 openings
      hpoint hbox hz hsucc hxor ha hn hc hr hsnapshot hroot hfrontier hasset hamount
  refine ⟨semantic, hrun, hcan, ?_⟩
  exact coefficients_of_packed_equations semantic point public1 openings hwide

/-- The combined coefficient vector retains the independently sourced first
four Poseidon lanes, the proved semantic block, and the caller's copy seed. -/
def lanesFromModels (poseidonModel : Fin 4 → ExactQM)
    (semanticLane : Fin 24 → ExactQM) (copyModel : ExactQM) : Fin 29 → ExactQM := fun i =>
  if h0 : i.val < 4 then poseidonModel ⟨i.val, h0⟩
  else if h28 : i.val < 28 then semanticLane ⟨i.val - 4, by omega⟩
  else copyModel

/-- The exact actual-source semantic coefficients remove `hsemantic` from the
old fold theorem.  The remaining poseidon/copy canonicality and source-value
facts are parameters of these actual caller outputs, not loop assumptions. -/
theorem prepared_folds_actual_semantic
    (point : Array QM 10#usize) (selectors : Selectors)
    (public1 : Public) (openings : Openings)
    (poseidon : Array QM 4#usize) (theta copySeed : QM)
    (poseidonModel : Fin 4 → ExactQM) (copyModel : ExactQM)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hz : CanonicalArray openings.z) (hsucc : CanonicalArray openings.succ_z)
    (hxor : CanonicalArray openings.xor12_z)
    (ha : AspisR1.DigestFixedPrefix.DigestWordsCanonical public1.anchor)
    (hn : AspisR1.DigestFixedPrefix.DigestWordsCanonical public1.nullifier)
    (hc : AspisR1.DigestFixedPrefix.DigestWordsCanonical public1.change)
    (hr : ∀ recipient, public1.recipient = some recipient → AspisR1.DigestFixedPrefix.DigestWordsCanonical recipient)
    (hsnapshot : ∀ j : Fin 20, AspisR1.DigestFixedPrefix.DigestWordsCanonical
      (public1.transition.live_snapshot.frontier.val[j.val]'(by
        simpa [public1.transition.live_snapshot.frontier.property] using j.isLt)))
    (hroot : AspisR1.DigestFixedPrefix.DigestWordsCanonical public1.transition.candidate_afterstate.next_root)
    (hfrontier : ∀ j : Fin 20, AspisR1.DigestFixedPrefix.DigestWordsCanonical
      (public1.transition.candidate_afterstate.next_frontier.val[j.val]'(by
        simpa [public1.transition.candidate_afterstate.next_frontier.property] using j.isLt)))
    (hasset : public1.asset_id.val < AspisR1.TerminalLiftM31Exact.P)
    (hamount : (AspisR1.ScalarSuffixExecution.amountValue public1).val < AspisR1.TerminalLiftM31Exact.P)
    (htheta : AspisR1.ExtractedMaskTowerAdd.CanonicalQM theta)
    (hcopy : AspisR1.ExtractedMaskTowerAdd.CanonicalQM copySeed)
    (hposeidon : ∀ i : Fin 4, AspisR1.ExtractedMaskTowerAdd.CanonicalQM
      (poseidon.val[i.val]'(by simpa [poseidon.property] using i.isLt)))
    (hcopyModel : AspisR1.ExtractedMaskQM31Exact.decode copySeed = copyModel)
    (hposeidonModel : ∀ i : Fin 4,
      AspisR1.ExtractedMaskQM31Exact.decode
        (poseidon.val[i.val]'(by simpa [poseidon.property] using i.isLt)) =
          poseidonModel i) :
    ∃ semantic : Array QM 24#usize, ∃ prepared : AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier,
      ∃ middle out : QM,
      AspisR1SemanticPackedBoundedCandidate.pool_v1.pair_forest_semantic_terminal.semantic_packed
        public1 openings selectors = .ok semantic ∧
      AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new theta = .ok prepared ∧
      pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
        (AspisR1.TerminalCompositionPolynomial.reverseRange 24#usize) semantic prepared copySeed = .ok middle ∧
      pool_v1.pair_forest_semantic_terminal.composition_parts_loop1
        (AspisR1.TerminalCompositionPolynomial.reverseRange 4#usize) poseidon prepared middle = .ok out ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out =
        ∑ i : Fin 29, AspisR1.ExtractedMaskQM31Exact.decode theta ^ i.val *
          (lanesFromModels poseidonModel (fun j => semanticLane24 public1 openings point j) copyModel) i := by
  obtain ⟨semantic, hsemanticRun, hsemanticCan, hcoeff⟩ :=
    actual_semantic_coefficients point selectors public1 openings hpoint hbox hz hsucc hxor
      ha hn hc hr hsnapshot hroot hfrontier hasset hamount
  have hsemanticCanonical := hsemanticCan
  let lane : Fin 29 → ExactQM :=
    lanesFromModels poseidonModel (fun j => semanticLane24 public1 openings point j) copyModel
  have hsemantic : ∀ i : Fin 24,
      AspisR1.TerminalCompositionLoopAdapter.coefficient24 semantic i.val =
        lane (Fin.natAdd 4 (Fin.castAdd 1 i)) := by
    intro i
    have hcoeff' : AspisR1.TerminalCompositionLoopAdapter.coefficient24 semantic i.val =
        semanticLane24 public1 openings point i := by
      simpa [AspisR1.TerminalCompositionLoopAdapter.coefficient24,
        AspisR1.PreweightedLoopModel.decoded, i.isLt] using hcoeff i
    rw [hcoeff']
    let shifted := Fin.natAdd 4 (Fin.castAdd 1 i)
    have hv : shifted.val = 4 + i.val := by simp [shifted]
    have hlt0 : ¬ shifted.val < 4 := by rw [hv]; omega
    have hlt28 : shifted.val < 28 := by rw [hv]; omega
    have hidx : (⟨shifted.val - 4, by omega⟩ : Fin 24) = i := by
      apply Fin.ext
      change shifted.val - 4 = i.val
      omega
    change semanticLane24 public1 openings point i =
      lanesFromModels poseidonModel
        (fun j => semanticLane24 public1 openings point j) copyModel shifted
    simp only [lanesFromModels, dif_neg hlt0, dif_pos hlt28]
    exact congrArg (fun j : Fin 24 => semanticLane24 public1 openings point j) hidx.symm
  have hposeidonLane : ∀ i : Fin 4,
      AspisR1.TerminalCompositionLoopAdapter.coefficient4 poseidon i.val =
        lane (Fin.castAdd 25 i) := by
    intro i
    have hcoeff' : AspisR1.TerminalCompositionLoopAdapter.coefficient4 poseidon i.val =
        poseidonModel i := by
      simpa [AspisR1.TerminalCompositionLoopAdapter.coefficient4, i.isLt]
        using hposeidonModel i
    rw [hcoeff']
    simp [lane, lanesFromModels]
  have hcopyLane : AspisR1.ExtractedMaskQM31Exact.decode copySeed = lane 28 := by
    simpa [lane, lanesFromModels] using hcopyModel
  obtain ⟨prepared, middle, out, hnew, hfirst, hsecond, hout, hsum⟩ :=
    AspisR1.TerminalCompositionPolynomial.prepared_folds_eq_lane_sum semantic poseidon theta copySeed
      lane htheta hcopy hsemanticCan hposeidon hsemantic hposeidonLane hcopyLane
  refine ⟨semantic, prepared, middle, out, hsemanticRun, hnew, hfirst, hsecond, hout, ?_⟩
  exact hsum

#print axioms coefficients_of_packed_equations
#print axioms actual_semantic_coefficients
#print axioms prepared_folds_actual_semantic
end
end AspisR1.SemanticCompositionCoefficients
