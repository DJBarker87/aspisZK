import SumHighTwoRanges
import InitialVariantExact
import PathSelectorPrefix

/-! Source-order selector prefix of semantic_initial_and_absorption.
All reads and field operations are derived on the same actual boxed point. -/
set_option autoImplicit false
namespace AspisR1.InitialSelectorPrefix
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.SumHighInnerLoop
open AspisR1.ExtractedMaskQM31Exact
abbrev Variant := pool_v1.pair_forest_semantic_terminal.CompiledVariant
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector

structure Registers (T : Type) where
  high0 : T
  high1 : T
  high25 : T
  high30 : T
  nodes : T
  transfer : T
  fixed : T
  privateEight : T
  privateTwo : T
  low0 : T
  full : T
  rate : T

def decodeRegisters (r : Registers QM) : Registers ExactQM where
  high0 := decode r.high0
  high1 := decode r.high1
  high25 := decode r.high25
  high30 := decode r.high30
  nodes := decode r.nodes
  transfer := decode r.transfer
  fixed := decode r.fixed
  privateEight := decode r.privateEight
  privateTwo := decode r.privateTwo
  low0 := decode r.low0
  full := decode r.full
  rate := decode r.rate

def canonicalRegisters (r : Registers QM) : Prop :=
  Canonical r.high0 ∧ Canonical r.high1 ∧ Canonical r.high25 ∧ Canonical r.high30 ∧ Canonical r.nodes ∧ Canonical r.transfer ∧ Canonical r.fixed ∧ Canonical r.privateEight ∧ Canonical r.privateTwo ∧ Canonical r.low0 ∧ Canonical r.full ∧ Canonical r.rate

def model {K : Type} [Field K] (v : R0P.Variant) (sel : R0P.Sel K) : Registers K :=
  let h := R0P.g2High sel
  let low0 := R0P.g2Low sel 0
  let nodes := R0P.scheduleNodes sel
  let vt := R0P.scheduleVariantSelectors v (h 27) (h 28) (h 29)
  let common := ((h 0 + h 1) + h 25) + h 30
  { high0 := h 0, high1 := h 1, high25 := h 25, high30 := h 30, nodes := nodes, transfer := vt.1, fixed := vt.2.1,
    privateEight := vt.2.2.1, privateTwo := vt.2.2.2, low0 := low0,
    full := low0 * ((common + vt.1) + vt.2.1), rate := low0 * nodes }

def run (v : Variant) (selectors : Selectors) : Result (Registers QM) := do
  let nodes ← AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high selectors
    (AspisR1.SumHighTwoRanges.pair AspisR1.SumHighTwoRanges.nodeRange1 AspisR1.SumHighTwoRanges.nodeRange2)
  let high0 ← Array.index_usize selectors.high 0#usize
  let high1 ← Array.index_usize selectors.high 1#usize
  let sum01 ← field.QM31.add high0 high1
  let high25 ← Array.index_usize selectors.high 25#usize
  let sum0125 ← field.QM31.add sum01 high25
  let high30 ← Array.index_usize selectors.high 30#usize
  let common ← field.QM31.add sum0125 high30
  let high27 ← Array.index_usize selectors.high 27#usize
  let high28 ← Array.index_usize selectors.high 28#usize
  let high29 ← Array.index_usize selectors.high 29#usize
  let (transfer, fixed, privateEight, privateTwo) ←
    AspisR1InitialVariantCandidate.pool_v1.pair_forest_semantic_terminal.initial_variant_selectors v high27 high28 high29
  let low0 ← Array.index_usize selectors.low 0#usize
  let sumFirst ← field.QM31.add common transfer
  let sumFull ← field.QM31.add sumFirst fixed
  let full ← field.QM31.mul low0 sumFull
  let rate ← field.QM31.mul low0 nodes
  .ok { high0 := high0, high1 := high1, high25 := high25, high30 := high30, nodes := nodes, transfer := transfer, fixed := fixed, privateEight := privateEight, privateTwo := privateTwo, low0 := low0, full := full, rate := rate }

attribute [local irreducible] R0P.g2High R0P.g2Low R0P.g2SumHigh R0P.scheduleNodes

theorem same_boxed_success (point : Array QM 10#usize) (selectors : Selectors) (v : Variant)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors) :
    ∃ r, run v selectors = .ok r ∧ canonicalRegisters r ∧
      decodeRegisters r = model (AspisR1.InitialVariantExact.modelVariant v) (pointSelector point) := by
  obtain ⟨hhigh, hlow, hhighModel, hlowModel⟩ :=
    AspisR1.SelectorMarginalModel.boxed_marginals point selectors hpoint hbox
  obtain ⟨nodes, hnodes, hcnodes, hvnodes⟩ :=
    AspisR1.SumHighTwoRanges.boxed_nodes point selectors hpoint hbox
  obtain ⟨h0, hr0, hc0, hv0⟩ := readHigh_success selectors 0#usize (by scalar_tac) hhigh
  have hn0 : (0#usize).val = 0 := by scalar_tac
  simp only [hn0] at hv0
  have hm0 := hhighModel (0 : Fin 64)
  change highAt selectors 0 = R0P.g2High (pointSelector point) 0 at hm0
  have hd0 := hv0.trans hm0
  obtain ⟨h1, hr1, hc1, hv1⟩ := readHigh_success selectors 1#usize (by scalar_tac) hhigh
  have hn1 : (1#usize).val = 1 := by scalar_tac
  simp only [hn1] at hv1
  have hm1 := hhighModel (1 : Fin 64)
  change highAt selectors 1 = R0P.g2High (pointSelector point) 1 at hm1
  have hd1 := hv1.trans hm1
  obtain ⟨h25, hr25, hc25, hv25⟩ := readHigh_success selectors 25#usize (by scalar_tac) hhigh
  have hn25 : (25#usize).val = 25 := by scalar_tac
  simp only [hn25] at hv25
  have hm25 := hhighModel (25 : Fin 64)
  change highAt selectors 25 = R0P.g2High (pointSelector point) 25 at hm25
  have hd25 := hv25.trans hm25
  obtain ⟨h30, hr30, hc30, hv30⟩ := readHigh_success selectors 30#usize (by scalar_tac) hhigh
  have hn30 : (30#usize).val = 30 := by scalar_tac
  simp only [hn30] at hv30
  have hm30 := hhighModel (30 : Fin 64)
  change highAt selectors 30 = R0P.g2High (pointSelector point) 30 at hm30
  have hd30 := hv30.trans hm30
  obtain ⟨h27, hr27, hc27, hv27⟩ := readHigh_success selectors 27#usize (by scalar_tac) hhigh
  have hn27 : (27#usize).val = 27 := by scalar_tac
  simp only [hn27] at hv27
  have hm27 := hhighModel (27 : Fin 64)
  change highAt selectors 27 = R0P.g2High (pointSelector point) 27 at hm27
  have hd27 := hv27.trans hm27
  obtain ⟨h28, hr28, hc28, hv28⟩ := readHigh_success selectors 28#usize (by scalar_tac) hhigh
  have hn28 : (28#usize).val = 28 := by scalar_tac
  simp only [hn28] at hv28
  have hm28 := hhighModel (28 : Fin 64)
  change highAt selectors 28 = R0P.g2High (pointSelector point) 28 at hm28
  have hd28 := hv28.trans hm28
  obtain ⟨h29, hr29, hc29, hv29⟩ := readHigh_success selectors 29#usize (by scalar_tac) hhigh
  have hn29 : (29#usize).val = 29 := by scalar_tac
  simp only [hn29] at hv29
  have hm29 := hhighModel (29 : Fin 64)
  change highAt selectors 29 = R0P.g2High (pointSelector point) 29 at hm29
  have hd29 := hv29.trans hm29
  obtain ⟨sum01, hs01, hcs01, hvs01⟩ := current_qm_add_exact h0 h1 hc0 hc1
  obtain ⟨sum0125, hs0125, hcs0125, hvs0125⟩ := current_qm_add_exact sum01 h25 hcs01 hc25
  obtain ⟨common, hcommon, hccommon, hvcommon⟩ := current_qm_add_exact sum0125 h30 hcs0125 hc30
  obtain ⟨vt, hvt, hctransfer, hcfixed, hcEight, hcTwo, hvtuple⟩ :=
    AspisR1.InitialVariantExact.source_success v h27 h28 h29 hc27 hc28 hc29
  rcases vt with ⟨transfer, fixed, privateEight, privateTwo⟩
  change (decode transfer, decode fixed, decode privateEight, decode privateTwo) = _ at hvtuple
  have ht := congrArg Prod.fst hvtuple
  have hf := congrArg (fun t : ExactQM × ExactQM × ExactQM × ExactQM => t.2.1) hvtuple
  have he := congrArg (fun t : ExactQM × ExactQM × ExactQM × ExactQM => t.2.2.1) hvtuple
  have htwo := congrArg (fun t : ExactQM × ExactQM × ExactQM × ExactQM => t.2.2.2) hvtuple
  dsimp only at ht hf he htwo
  obtain ⟨low0, hlow0, hclow0, hvlow0⟩ := AspisR1.PathSelectorPrefix.readLow_success selectors 0#usize (by scalar_tac) hlow
  have hmLow := hlowModel (0 : Fin 16)
  change AspisR1.PathSelectorPrefix.lowAt selectors 0 = R0P.g2Low (pointSelector point) 0 at hmLow
  simp only [hn0] at hvlow0
  have hdLow := hvlow0.trans hmLow
  obtain ⟨sumFirst, hsFirst, hcsFirst, hvsFirst⟩ := current_qm_add_exact common transfer hccommon hctransfer
  obtain ⟨sumFull, hsFull, hcsFull, hvsFull⟩ := current_qm_add_exact sumFirst fixed hcsFirst hcfixed
  obtain ⟨full, hfull, hcfull, hvfull⟩ := current_qm_mul_exact low0 sumFull hclow0 hcsFull
  obtain ⟨rate, hrate, hcrate, hvrate⟩ := current_qm_mul_exact low0 nodes hclow0 hcnodes
  refine ⟨{ high0 := h0, high1 := h1, high25 := h25, high30 := h30, nodes := nodes, transfer := transfer, fixed := fixed, privateEight := privateEight, privateTwo := privateTwo, low0 := low0, full := full, rate := rate }, ?_, ?_, ?_⟩
  · simp only [run, hnodes, bind_tc_ok, hr0, hr1, hs01, hr25, hs0125,
      hr30, hcommon, hr27, hr28, hr29, AspisR1.InitialVariantExact.source,
      hvt, hlow0, hsFirst, hsFull, hfull, hrate]
    change ((do
      let sumFirst ← field.QM31.add common transfer
      let sumFull ← field.QM31.add sumFirst fixed
      let full ← field.QM31.mul low0 sumFull
      Result.ok { high0 := h0, high1 := h1, high25 := h25, high30 := h30, nodes := nodes, transfer := transfer, fixed := fixed, privateEight := privateEight, privateTwo := privateTwo, low0 := low0, full := full, rate := rate }) : Result (Registers QM)) = _
    simp only [hsFirst, hsFull, hfull, bind_tc_ok]
  · exact ⟨hc0, hc1, hc25, hc30, hcnodes, hctransfer, hcfixed, hcEight, hcTwo, hclow0, hcfull, hcrate⟩
  · simp only [decodeRegisters, model]
    rw [hvfull, hvrate, hvsFull, hvsFirst, hvcommon, hvs0125, hvs01,
      ht, hf, he, htwo, hd0, hd1, hd25, hd30, hd27, hd28, hd29, hdLow, hvnodes]

#print axioms same_boxed_success
end
end AspisR1.InitialSelectorPrefix
