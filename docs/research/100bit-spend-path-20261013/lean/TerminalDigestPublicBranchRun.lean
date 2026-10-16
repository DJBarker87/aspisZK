import TerminalDigestPublicLoopSource
import TerminalDigestPublicBranchModel
import TerminalDigestPublicBranchCall
import TerminalDigestPublicTargetActual
import TerminalDigestPublicRowAddressOps
import TerminalDigestPublicRowExtended
import DigestFixedPrefixR0P
import AspisR1TerminalDigestBindingCandidate.LoopExact

set_option autoImplicit false
namespace AspisR1TerminalDigestPublicLoop.BranchRun
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1TerminalDigestBindingCandidate.LoopExact
abbrev QM := field.QM31
abbrev M31 := field.M31
abbrev U64 := UScalar UScalarTy.U64
abbrev Usize := UScalar UScalarTy.Usize
abbrev ExactQM := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev Snapshot := pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings

private def decodedDigest (a : Array QM 8#usize) : R0P.Digest ExactQM :=
  fun j => AspisR1.ExtractedMaskQM31Exact.decode (cellAt a j.val)
private def decodedOpenings (a : Array QM 16#usize) : Fin 16 → ExactQM :=
  fun i => AspisR1.ExtractedMaskQM31Exact.decode (openedAt a i.val)

/-- The exact generated branch body, ending immediately before its recursive
outer-loop call. -/
def run (level : Usize) (source : Snapshot) (a : Array QM 16#usize)
    (selectors : Selectors) (digests : Array QM 8#usize) : Result (Array QM 8#usize) := do
  let block ← 34#usize + level
  let i ← source.next_pair_index >>> level
  let i1 ← lift (i &&& 1#u64)
  if i1 = 0#u64 then
    let i2 ← block * 16#usize
    let q ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i2
    let a1 ← AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root level
    AspisR1TerminalDigestBindingCandidate.add_digest_binding
      digests q a AspisR1AbsorptionCandidate.poseidon2.RATE a1 true
  else
    let i2 ← block * 16#usize
    let i3 ← i2 + 12#usize
    let q ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i3
    let a1 ← Array.index_usize source.frontier level
    AspisR1TerminalDigestBindingCandidate.add_digest_binding
      digests q a 0#usize a1 false

/-- One literal generated outer-loop branch, including checked row-address
arithmetic, boxed selector lookup, M31 target operation, and binding update,
implements one retained `frontierStep`. -/
theorem run_success
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (point : Array QM 10#usize) (selectors : Selectors) (source : Snapshot)
    (level : Usize) (hlevel : level.val < 20)
    (openings : Openings)
    (digests : Array QM 8#usize)
    (hsource : source = public1.transition.live_snapshot)
    (hpoint : AspisR1.SelectorExpansionCorrectness.canonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hopened : CanonicalArray openings.z) (hdigests : CanonicalArray digests)
    (hfrontierCanonical : ∀ k : Fin 20, TargetActual.CanonicalM31
      (source.frontier.val[k.val]'(by
        simpa [source.frontier.property] using k.isLt))) :
    ∃ out, run level source openings.z selectors digests = .ok out ∧ CanonicalArray out ∧
      decodedDigest out = AspisR1TerminalDigestPublicLoop.Model.frontierStep
        (AspisR1.SemanticPublicModel.exactPublic public1)
        (AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings openings)
        (fun i => AspisR1.SelectorValueLaneModelComposition.pointSelector point i)
        (decodedDigest digests) ⟨level.val, hlevel⟩ := by
  obtain ⟨_, bit, hshift, hbitrun, hbit⟩ :=
    AspisR1TerminalDigestPublicLoop.BranchModel.live_snapshot_branch public1 level hlevel
  obtain ⟨block, base, plus, hblock, hblockVal, hbase, hbaseVal, hplus, hplusVal⟩ :=
    AspisR1TerminalDigestPublicLoop.RowAddressOps.source_row_addresses level hlevel
  have hopenedModel : decodedOpenings openings.z =
      (AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings openings).z := by
    have h := AspisR1.DigestFixedPrefix.R0PBridge.opened_model openings
    change AspisR1.DigestFixedBinding.openedModel openings.z = _ at h
    change decodedOpenings openings.z = _
    exact h
  have hfrontier := hfrontierCanonical
  by_cases hb : bit = (0#u64)
  · have hbitZero : True ↔ R0P.digestBitZero
        (AspisR1.SemanticPublicModel.exactPublic public1) ⟨level.val, hlevel⟩ := by
      constructor
      · intro _
        exact hbit.mp hb
      · intro _
        trivial
    have hrowBound : base.val < 1024 := by rw [hbaseVal]; omega
    have hrow : base.val = (34 + level.val) * 16 + if True then 0 else 12 := by
      rw [hbaseVal]
      simp
    have htargetRun := AspisR1.EmptyRootBindingModel.source_right_target level hlevel
    rcases htargetRun with ⟨expected, hexpectedRun, hexpectedCan, hexpectedValue⟩
    have hstartVal : (AspisR1AbsorptionCandidate.poseidon2.RATE).val = 8 := by
      unfold AspisR1AbsorptionCandidate.poseidon2.RATE
      scalar_tac
    have hbranch : (true = true) ↔ R0P.digestBitZero
        (AspisR1.SemanticPublicModel.exactPublic public1) ⟨level.val, hlevel⟩ := by
      simpa using hbitZero
    have hactual :
        AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root level =
          .ok expected := hexpectedRun
    obtain ⟨hcanExpected', htargetModel'⟩ :=
      AspisR1TerminalDigestPublicLoop.TargetActual.source_target
        public1 source level hlevel hsource expected true hbranch hfrontier hactual
    have hrate : AspisR1AbsorptionCandidate.poseidon2.RATE.val = 8 := by
      unfold AspisR1AbsorptionCandidate.poseidon2.RATE
      scalar_tac
    have hrateBound : AspisR1AbsorptionCandidate.poseidon2.RATE.val + 8 ≤ 16 := by omega
    have hexpected : ∀ j : Fin 8,
        (expected.val[j.val]'(by simpa [expected.property] using j.isLt)).val <
          AspisR1.ExtractedMaskTowerAdd.P := hcanExpected'
    obtain ⟨q, out, hqrun, hqcan, _, hcall, houtcan, hmodel⟩ :=
      AspisR1TerminalDigestPublicLoop.BranchCall.binding_call
        (AspisR1.SemanticPublicModel.exactPublic public1)
        (AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings openings)
        point selectors ⟨level.val,hlevel⟩ base True digests openings.z
        AspisR1AbsorptionCandidate.poseidon2.RATE expected true
        hrowBound hrow hbitZero (by simp [hb]) (by simp [hrate]) hpoint hbox
        hdigests hopened hexpected hopenedModel htargetModel'
    refine ⟨out, ?_, houtcan, hmodel⟩
    simp only [run, hsource, hblock, hshift, hbitrun, bind_tc_ok]
    simp [hb, hbase, hqrun, hexpectedRun, hcall]
  · have hnotbit : ¬ bit = (0#u64) := hb
    have hbitZero : False ↔ R0P.digestBitZero
        (AspisR1.SemanticPublicModel.exactPublic public1) ⟨level.val, hlevel⟩ := by
      constructor
      · intro h
        exact False.elim h
      · intro h
        have : bit = (0#u64) := hbit.mpr h
        exact (hnotbit this).elim
    have hrowBound : plus.val < 1024 := by rw [hplusVal]; omega
    have hrow : plus.val = (34 + level.val) * 16 + if False then 0 else 12 := by
      rw [hplusVal]
      simp
    have h20 : (20#usize).val = 20 := by scalar_tac
    have hlevelBound : level.val < source.frontier.length := by
      simpa [source.frontier.property, h20] using hlevel
    obtain ⟨expected, hexpectedRun, hexpectedValue⟩ :=
      WP.spec_imp_exists (Array.index_usize_spec source.frontier level hlevelBound)
    have hbranch : (false = true) ↔ R0P.digestBitZero
        (AspisR1.SemanticPublicModel.exactPublic public1) ⟨level.val, hlevel⟩ := by
      constructor
      · intro h
        cases h
      · intro h
        have : bit = (0#u64) := hbit.mpr h
        exact (hnotbit this).elim
    obtain ⟨hcanExpected', htargetModel'⟩ :=
      AspisR1TerminalDigestPublicLoop.TargetActual.source_target
        public1 source level hlevel hsource expected false hbranch hfrontier hexpectedRun
    have hexpectedRun' :
        public1.transition.live_snapshot.frontier.index_usize level = .ok expected := by
      simpa [hsource] using hexpectedRun
    have hzeroVal : (0#usize).val = 0 := by scalar_tac
    have hexpected : ∀ j : Fin 8,
        (expected.val[j.val]'(by simpa [expected.property] using j.isLt)).val <
          AspisR1.ExtractedMaskTowerAdd.P := hcanExpected'
    obtain ⟨q, out, hqrun, hqcan, _, hcall, houtcan, hmodel⟩ :=
      AspisR1TerminalDigestPublicLoop.BranchCall.binding_call
        (AspisR1.SemanticPublicModel.exactPublic public1)
        (AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings openings)
        point selectors ⟨level.val,hlevel⟩ plus False digests openings.z
        (0#usize) expected false hrowBound hrow hbitZero (by simp [hnotbit]) (by simp [hzeroVal])
        hpoint hbox hdigests hopened hexpected hopenedModel htargetModel'
    refine ⟨out, ?_, houtcan, hmodel⟩
    simp only [run, hsource, hblock, hshift, hbitrun, bind_tc_ok]
    simp [hnotbit, hbase, hplus, hqrun, hexpectedRun, hexpectedRun', hcall]

#print axioms run_success
end AspisR1TerminalDigestPublicLoop.BranchRun
