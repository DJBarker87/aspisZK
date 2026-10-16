import InitialSelectorPrefix
import AbsorptionLiteralExecution

/-! Actual remaining absorption-selector source chain, with the same boxed
point and already-derived prefix registers. -/
set_option autoImplicit false
namespace AspisR1.AbsorptionSelectorSetup
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.SumHighInnerLoop
open AspisR1.ExtractedMaskQM31Exact
abbrev QM := field.QM31
abbrev Canonical := CurrentCanonicalQM
abbrev Prefix := AspisR1.InitialSelectorPrefix.Registers QM
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector

structure Registers (T : Type) where
  low : T
  fixed : T
  two : T
  eight : T
  nodes : T

def decodeRegisters (r : Registers QM) : Registers ExactQM where
  low := decode r.low
  fixed := decode r.fixed
  two := decode r.two
  eight := decode r.eight
  nodes := decode r.nodes

def canonicalRegisters (r : Registers QM) : Prop :=
  Canonical r.low ∧ Canonical r.fixed ∧ Canonical r.two ∧ Canonical r.eight ∧ Canonical r.nodes

def model {K : Type} [Field K] (v : R0P.Variant) (sel : R0P.Sel K) : Registers K :=
  let h := R0P.g2High sel
  let p := AspisR1.InitialSelectorPrefix.model v sel
  { low := R0P.g2Low sel 12, fixed := p.fixed,
    two := (h 3 + h 32) + p.privateTwo,
    eight := ((((((h 0 + h 1) + h 2) + h 25) + h 26) + h 30) + h 31) + p.privateEight,
    nodes := p.nodes }

def run (p : Prefix) (selectors : Selectors) : Result (Registers QM) := do
  let q28 ← field.QM31.add p.high0 p.high1
  let h2 ← Array.index_usize selectors.high 2#usize
  let q30 ← field.QM31.add q28 h2
  let q31 ← field.QM31.add q30 p.high25
  let h26 ← Array.index_usize selectors.high 26#usize
  let q33 ← field.QM31.add q31 h26
  let q34 ← field.QM31.add q33 p.high30
  let h31 ← Array.index_usize selectors.high 31#usize
  let eight ← field.QM31.add q34 h31
  let h3 ← Array.index_usize selectors.high 3#usize
  let h32 ← Array.index_usize selectors.high 32#usize
  let two ← field.QM31.add h3 h32
  let eight1 ← field.QM31.add eight p.privateEight
  let two1 ← field.QM31.add two p.privateTwo
  let low ← Array.index_usize selectors.low 12#usize
  .ok { low := low, fixed := p.fixed, two := two1, eight := eight1, nodes := p.nodes }

attribute [local irreducible] R0P.g2High R0P.g2Low R0P.g2SumHigh R0P.scheduleNodes

theorem source_success (point : Array QM 10#usize) (selectors : Selectors)
    (v : R0P.Variant) (p : Prefix)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hc : AspisR1.InitialSelectorPrefix.canonicalRegisters p)
    (hm : AspisR1.InitialSelectorPrefix.decodeRegisters p =
      AspisR1.InitialSelectorPrefix.model v (pointSelector point)) :
    ∃ out, run p selectors = .ok out ∧ canonicalRegisters out ∧
      decodeRegisters out = model v (pointSelector point) := by
  rcases hc with ⟨hc0, hc1, hc25, hc30, hcnodes, hct, hcfixed, hcEight, hcTwo, hclow0, hcfull, hcrate⟩
  obtain ⟨hhigh, hlow, hhighModel, hlowModel⟩ :=
    AspisR1.SelectorMarginalModel.boxed_marginals point selectors hpoint hbox
  have hp_high0 := congrArg AspisR1.InitialSelectorPrefix.Registers.high0 hm
  simp only [AspisR1.InitialSelectorPrefix.decodeRegisters, AspisR1.InitialSelectorPrefix.model] at hp_high0
  have hp_high1 := congrArg AspisR1.InitialSelectorPrefix.Registers.high1 hm
  simp only [AspisR1.InitialSelectorPrefix.decodeRegisters, AspisR1.InitialSelectorPrefix.model] at hp_high1
  have hp_high25 := congrArg AspisR1.InitialSelectorPrefix.Registers.high25 hm
  simp only [AspisR1.InitialSelectorPrefix.decodeRegisters, AspisR1.InitialSelectorPrefix.model] at hp_high25
  have hp_high30 := congrArg AspisR1.InitialSelectorPrefix.Registers.high30 hm
  simp only [AspisR1.InitialSelectorPrefix.decodeRegisters, AspisR1.InitialSelectorPrefix.model] at hp_high30
  have hp_nodes := congrArg AspisR1.InitialSelectorPrefix.Registers.nodes hm
  simp only [AspisR1.InitialSelectorPrefix.decodeRegisters, AspisR1.InitialSelectorPrefix.model] at hp_nodes
  have hp_fixed := congrArg AspisR1.InitialSelectorPrefix.Registers.fixed hm
  simp only [AspisR1.InitialSelectorPrefix.decodeRegisters, AspisR1.InitialSelectorPrefix.model] at hp_fixed
  have hp_privateEight := congrArg AspisR1.InitialSelectorPrefix.Registers.privateEight hm
  simp only [AspisR1.InitialSelectorPrefix.decodeRegisters, AspisR1.InitialSelectorPrefix.model] at hp_privateEight
  have hp_privateTwo := congrArg AspisR1.InitialSelectorPrefix.Registers.privateTwo hm
  simp only [AspisR1.InitialSelectorPrefix.decodeRegisters, AspisR1.InitialSelectorPrefix.model] at hp_privateTwo
  obtain ⟨h2, hr2, hc2, hv2⟩ := readHigh_success selectors 2#usize (by scalar_tac) hhigh
  have hn2 : (2#usize).val = 2 := by scalar_tac
  simp only [hn2] at hv2
  have hm2 := hhighModel (2 : Fin 64)
  change highAt selectors 2 = R0P.g2High (pointSelector point) 2 at hm2
  have hd2 := hv2.trans hm2
  obtain ⟨h26, hr26, hc26, hv26⟩ := readHigh_success selectors 26#usize (by scalar_tac) hhigh
  have hn26 : (26#usize).val = 26 := by scalar_tac
  simp only [hn26] at hv26
  have hm26 := hhighModel (26 : Fin 64)
  change highAt selectors 26 = R0P.g2High (pointSelector point) 26 at hm26
  have hd26 := hv26.trans hm26
  obtain ⟨h31, hr31, hc31, hv31⟩ := readHigh_success selectors 31#usize (by scalar_tac) hhigh
  have hn31 : (31#usize).val = 31 := by scalar_tac
  simp only [hn31] at hv31
  have hm31 := hhighModel (31 : Fin 64)
  change highAt selectors 31 = R0P.g2High (pointSelector point) 31 at hm31
  have hd31 := hv31.trans hm31
  obtain ⟨h3, hr3, hc3, hv3⟩ := readHigh_success selectors 3#usize (by scalar_tac) hhigh
  have hn3 : (3#usize).val = 3 := by scalar_tac
  simp only [hn3] at hv3
  have hm3 := hhighModel (3 : Fin 64)
  change highAt selectors 3 = R0P.g2High (pointSelector point) 3 at hm3
  have hd3 := hv3.trans hm3
  obtain ⟨h32, hr32, hc32, hv32⟩ := readHigh_success selectors 32#usize (by scalar_tac) hhigh
  have hn32 : (32#usize).val = 32 := by scalar_tac
  simp only [hn32] at hv32
  have hm32 := hhighModel (32 : Fin 64)
  change highAt selectors 32 = R0P.g2High (pointSelector point) 32 at hm32
  have hd32 := hv32.trans hm32
  obtain ⟨q28, hrq28, hcq28, hvq28⟩ := current_qm_add_exact p.high0 p.high1 hc0 hc1
  obtain ⟨q30, hrq30, hcq30, hvq30⟩ := current_qm_add_exact q28 h2 hcq28 hc2
  obtain ⟨q31, hrq31, hcq31, hvq31⟩ := current_qm_add_exact q30 p.high25 hcq30 hc25
  obtain ⟨q33, hrq33, hcq33, hvq33⟩ := current_qm_add_exact q31 h26 hcq31 hc26
  obtain ⟨q34, hrq34, hcq34, hvq34⟩ := current_qm_add_exact q33 p.high30 hcq33 hc30
  obtain ⟨eight, hreight, hceight, hveight⟩ := current_qm_add_exact q34 h31 hcq34 hc31
  obtain ⟨two, hrtwo, hctwo, hvtwo⟩ := current_qm_add_exact h3 h32 hc3 hc32
  obtain ⟨eight1, hreight1, hceight1, hveight1⟩ := current_qm_add_exact eight p.privateEight hceight hcEight
  obtain ⟨two1, hrtwo1, hctwo1, hvtwo1⟩ := current_qm_add_exact two p.privateTwo hctwo hcTwo
  obtain ⟨low, hrlow, hclow, hvlow⟩ := AspisR1.PathSelectorPrefix.readLow_success selectors 12#usize (by scalar_tac) hlow
  have hn12 : (12#usize).val = 12 := by scalar_tac
  simp only [hn12] at hvlow
  have hmLow := hlowModel (12 : Fin 16)
  change AspisR1.PathSelectorPrefix.lowAt selectors 12 = R0P.g2Low (pointSelector point) 12 at hmLow
  have hdLow := hvlow.trans hmLow
  refine ⟨{ low := low, fixed := p.fixed, two := two1, eight := eight1, nodes := p.nodes }, ?_, ?_, ?_⟩
  · simp only [run, hrq28, bind_tc_ok, hr2, hrq30, hrq31, hr26, hrq33, hrq34,
      hr31, hreight, hr3, hr32, hrtwo, hreight1, hrtwo1, hrlow]
  · exact ⟨hclow, hcfixed, hctwo1, hceight1, hcnodes⟩
  · simp only [decodeRegisters, model, AspisR1.InitialSelectorPrefix.model]
    rw [hvtwo1, hveight1, hvtwo, hveight, hvq34, hvq33, hvq31, hvq30, hvq28,
      hp_high0, hp_high1, hp_high25, hp_high30, hp_nodes, hp_fixed,
      hp_privateEight, hp_privateTwo, hd2, hd26, hd31, hd3, hd32, hdLow]

#print axioms source_success
end
end AspisR1.AbsorptionSelectorSetup
