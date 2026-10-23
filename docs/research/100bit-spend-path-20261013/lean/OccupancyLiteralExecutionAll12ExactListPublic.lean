import OccupancyGeneratedSlice
import OccupancyLiteralPrefixReadsV2
import OccupancyLiteralLoop
import OccupancyLiteralTail
import OccupancyVectorBridge
import OccupancyExpectedBridge
import R0P.Occupancy
import ExtractedMaskConstants
import SelectorExpansionCorrectness

/-! Compose the actual generated occupancy literal source prefix, eight-cell
range loop, and final lane-11 update. This is a source execution bridge, not a
statement about later terminal packing. -/
set_option autoImplicit false
namespace AspisR1.OccupancyLiteralExecutionAll12ExactListPublic
noncomputable section
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQM31Exact

abbrev QM := field.QM31
abbrev Canonical := CurrentCanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Range := core.ops.range.Range Usize

def get16 (a : Array QM 16#usize) (i : Fin 16) : QM :=
  a.val[i.val]'(by simpa [a.property] using
    (by have h16 : (16#usize).val = 16 := by scalar_tac; omega : i.val < (16#usize).val))

def get12 (a : Array QM 12#usize) (i : Fin 12) : QM :=
  a.val[i.val]'(by simpa [a.property] using
    (by have h12 : (12#usize).val = 12 := by scalar_tac; omega : i.val < (12#usize).val))

def cellVector (a : Array QM 12#usize) : Fin 12 → ExactQM :=
  fun i => AspisR1.ExtractedMaskQM31Exact.decode
    (a.val[i.val]'(by simpa [a.property] using i.isLt))

@[irreducible] def modelLanes (input output expected : ExactQM) (opened : Fin 16 → ExactQM) :
    List ExactQM := R0P.occupancyLanesLiteral input output expected opened

theorem get12_eq_cellAt (a : Array QM 12#usize) (i : Fin 12) :
    get12 a i = AspisR1.OccupancyLiteralLoop.cellAt a i.val := by
  change a.val[i.val]'(by simpa [a.property] using i.isLt) =
    (if h : i.val < 12 then
      a.val[i.val]'(by simpa [a.property] using h)
     else field.QM31.ZERO)
  rw [dif_pos i.isLt]

theorem openedCell_eq_get16 (a : Array QM 16#usize) (i : Fin 16) :
    AspisR1.OccupancyLiteralLoop.openedCell a i.val = get16 a i := by
  have hi : i.val < a.val.length := by simpa [a.property] using i.isLt
  unfold AspisR1.OccupancyLiteralLoop.openedCell get16
  rw [List.getElem?_eq_getElem hi]
  rfl

def run (input output : QM) (expected : field.M31)
    (opened : Array QM 16#usize) : Result (Array QM 12#usize) := do
  let (occupied, oneMinus, both, _q8, initial) ←
    AspisR1.OccupancyLiteralPrefixReadsV2.prefixRun input output opened
  let iter := ({ start := 0#usize, «end» := poseidon2.DIGEST_ELEMS } : Range)
  let occupancy3 ← pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal_loop
    iter opened oneMinus initial both
  AspisR1.OccupancyLiteralTail.tailRun input output expected opened
    occupied oneMinus occupancy3

theorem generated_eq_run (input output : QM) (expected : field.M31)
    (opened : Array QM 16#usize) :
    pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal
      input output expected opened = run input output expected opened := by
  have uncurry_as_projections {α β γ : Type} (f : α → β → γ) :
      Aeneas.Std.uncurry f = fun p : α × β => f p.1 p.2 := by
    funext p
    rcases p with ⟨a, b⟩
    exact Aeneas.Std.uncurry_apply_pair f a b
  simp only [pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal,
    run, AspisR1.OccupancyLiteralPrefixReadsV2.prefixRun,
    AspisR1.OccupancyLiteralTail.tailRun, bind_assoc_eq, bind_tc_ok, uncurry_as_projections]

theorem literal_success
    (variant : pool_v1.pair_forest_semantic_terminal.CompiledVariant)
    (input output : QM) (opened : Array QM 16#usize)
    (hin : Canonical input) (hout : Canonical output)
    (hopened : CanonicalArray opened) :
    ∃ expected : field.M31, ∃ out : Array QM 12#usize,
      pool_v1.pair_forest_semantic_terminal.variant_expected_output variant = .ok expected ∧
      pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal
        input output expected opened = .ok out ∧ CanonicalArray out ∧
      List.ofFn (cellVector out) = R0P.occupancyLanesLiteral
        (AspisR1.ExtractedMaskQM31Exact.decode input)
        (AspisR1.ExtractedMaskQM31Exact.decode output)
        (R0P.occupancyExpected (AspisR1.OccupancyExpectedBridge.modelVariant variant))
        (fun i => AspisR1.ExtractedMaskQM31Exact.decode (get16 opened i)) := by
  obtain ⟨expected, expectedQ, hexpected, hlift, hcanExpected, hdecodeExpected⟩ :=
    AspisR1.OccupancyExpectedBridge.variant_expected_lift_exact variant
  obtain ⟨occupied, oneMinus, both, q8, initial, hprefix, hcanOccupied, hcanOneMinus, hcanBoth,
      hcanQ8, hcanInitial, hbothValue, hcell0, hcell1, hcell2, hoccupiedGet, honeMinusValue⟩ :=
    AspisR1.OccupancyLiteralPrefixReadsV2.prefix_success input output opened hin hout hopened
  let iter := ({ start := 0#usize, «end» := poseidon2.DIGEST_ELEMS } : Range)
  have hend : iter.end.val = 8 := by
    change (poseidon2.DIGEST_ELEMS).val = 8
    simp only [poseidon2.DIGEST_ELEMS]
    scalar_tac
  have hspan : iter.start.val + 8 = 8 := by
    dsimp [iter]
    scalar_tac
  have hprefixLoop : ∀ j : Fin 12, 3 ≤ j.val → j.val < 3 + iter.start.val →
      AspisR1.ExtractedMaskQM31Exact.decode
        (AspisR1.OccupancyLiteralLoop.cellAt initial j.val) =
          AspisR1.OccupancyLiteralLoop.laneValue opened oneMinus both j.val := by
    intro j hlo hhi
    have hs : 3 + iter.start.val = 3 := by dsimp [iter]; scalar_tac
    omega
  obtain ⟨loopOut, hloop, hcanLoopOut, hloopValues⟩ :=
    AspisR1.OccupancyLiteralLoop.loop_success_fuel opened oneMinus both initial iter 8
      hend hspan hopened hcanOneMinus hcanBoth hcanInitial hprefixLoop
  have hloopSource :
      pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal_loop
        ({ start := 0#usize, «end» := poseidon2.DIGEST_ELEMS } : Range)
        opened oneMinus initial both = .ok loopOut := by
    simpa only [iter] using hloop
  have hoccupied : Canonical occupied := hcanOccupied
  have hoccupiedGet' : occupied = get16 opened ⟨0, by decide⟩ := by
    change occupied = get16 opened ⟨0, by decide⟩ at hoccupiedGet
    exact hoccupiedGet
  have honeMinusValue' :
      AspisR1.ExtractedMaskQM31Exact.decode oneMinus =
        1 - AspisR1.ExtractedMaskQM31Exact.decode occupied := by
    have htmp := honeMinusValue
    rw [← hoccupiedGet] at htmp
    exact htmp
  have hcell0' := hcell0
  have hcell1' := hcell1
  have hcell2' := hcell2
  change AspisR1.ExtractedMaskQM31Exact.decode (get12 initial ⟨0, by decide⟩) =
    (AspisR1.ExtractedMaskQM31Exact.decode input + AspisR1.ExtractedMaskQM31Exact.decode output) *
      (AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨0, by decide⟩) *
        (AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨0, by decide⟩) - 1)) at hcell0'
  change AspisR1.ExtractedMaskQM31Exact.decode (get12 initial ⟨1, by decide⟩) =
    (AspisR1.ExtractedMaskQM31Exact.decode input + AspisR1.ExtractedMaskQM31Exact.decode output) *
      (AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨9, by decide⟩) *
          AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨1, by decide⟩) -
        AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨0, by decide⟩)) at hcell1'
  change AspisR1.ExtractedMaskQM31Exact.decode (get12 initial ⟨2, by decide⟩) =
    (AspisR1.ExtractedMaskQM31Exact.decode input + AspisR1.ExtractedMaskQM31Exact.decode output) *
      (AspisR1.ExtractedMaskQM31Exact.decode oneMinus *
        AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨1, by decide⟩)) at hcell2'
  obtain ⟨out, htail, hcanOut, hcell11, hframe⟩ :=
    AspisR1.OccupancyLiteralTail.tail_success input output expected variant opened
      occupied oneMinus loopOut hin hout hopened hoccupied hcanOneMinus hcanLoopOut
      honeMinusValue' hexpected
  refine ⟨expected, out, hexpected, ?_, hcanOut, ?_⟩
  rw [generated_eq_run input output expected opened]
  simp only [run, hprefix, bind_tc_ok, Aeneas.Std.uncurry_apply_pair, hloopSource, htail]
  have hcells : ∀ i : Fin 12,
      AspisR1.ExtractedMaskQM31Exact.decode (get12 out i) =
      (modelLanes
          (AspisR1.ExtractedMaskQM31Exact.decode input)
          (AspisR1.ExtractedMaskQM31Exact.decode output)
          (R0P.occupancyExpected (AspisR1.OccupancyExpectedBridge.modelVariant variant))
          (fun k => AspisR1.ExtractedMaskQM31Exact.decode (get16 opened k)))[i.val]'(by
            have hlen : (modelLanes
                (AspisR1.ExtractedMaskQM31Exact.decode input)
                (AspisR1.ExtractedMaskQM31Exact.decode output)
                (R0P.occupancyExpected (AspisR1.OccupancyExpectedBridge.modelVariant variant))
                (fun k => AspisR1.ExtractedMaskQM31Exact.decode (get16 opened k))).length = 12 := by
              simp [modelLanes, R0P.occupancyLanesLiteral]
            omega) := by
    intro i
    by_cases h11 : i.val = 11
    · have hi : i = ⟨11, by decide⟩ := Fin.ext h11
      subst i
      have hcell11local : AspisR1.ExtractedMaskQM31Exact.decode (get12 out ⟨11, by decide⟩) =
          AspisR1.ExtractedMaskQM31Exact.decode input *
            (AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨10, by decide⟩) *
              (1 - AspisR1.ExtractedMaskQM31Exact.decode occupied)) +
            AspisR1.ExtractedMaskQM31Exact.decode output *
              (AspisR1.ExtractedMaskQM31Exact.decode occupied -
                R0P.occupancyExpected (AspisR1.OccupancyExpectedBridge.modelVariant variant)) := by
        change AspisR1.ExtractedMaskQM31Exact.decode (get12 out ⟨11, by decide⟩) = _ at hcell11
        exact hcell11
      have hcell11local' := hcell11local
      rw [hoccupiedGet'] at hcell11local'
      simpa [modelLanes, R0P.occupancyLanesLiteral] using hcell11local' 
    · have hunchanged : get12 out i = get12 loopOut i := hframe i h11
      have hmodel : (modelLanes
          (AspisR1.ExtractedMaskQM31Exact.decode input)
          (AspisR1.ExtractedMaskQM31Exact.decode output)
          (R0P.occupancyExpected (AspisR1.OccupancyExpectedBridge.modelVariant variant))
          (fun k => AspisR1.ExtractedMaskQM31Exact.decode (get16 opened k)))[i.val]'(by
            have hlen : (modelLanes
                (AspisR1.ExtractedMaskQM31Exact.decode input)
                (AspisR1.ExtractedMaskQM31Exact.decode output)
                (R0P.occupancyExpected (AspisR1.OccupancyExpectedBridge.modelVariant variant))
                (fun k => AspisR1.ExtractedMaskQM31Exact.decode (get16 opened k))).length = 12 := by
              simp [modelLanes, R0P.occupancyLanesLiteral]
            omega) = AspisR1.ExtractedMaskQM31Exact.decode
              (AspisR1.OccupancyLiteralLoop.cellAt loopOut i.val) := by
        by_cases h0 : i.val = 0
        · have hi : i = ⟨0, by decide⟩ := Fin.ext h0
          subst i
          have hv := hloopValues ⟨0, by decide⟩
          have hv' : AspisR1.ExtractedMaskQM31Exact.decode
              (AspisR1.OccupancyLiteralLoop.cellAt loopOut 0) =
              AspisR1.ExtractedMaskQM31Exact.decode
                (AspisR1.OccupancyLiteralLoop.cellAt initial 0) := by simpa using hv
          have hinit : AspisR1.ExtractedMaskQM31Exact.decode
              (AspisR1.OccupancyLiteralLoop.cellAt initial 0) =
              (AspisR1.ExtractedMaskQM31Exact.decode input + AspisR1.ExtractedMaskQM31Exact.decode output) *
                (AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨0, by decide⟩) *
                  (AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨0, by decide⟩) - 1)) := by
            rw [← get12_eq_cellAt initial ⟨0, by decide⟩]
            exact hcell0'
          have hm : (modelLanes
              (AspisR1.ExtractedMaskQM31Exact.decode input)
              (AspisR1.ExtractedMaskQM31Exact.decode output)
              (R0P.occupancyExpected (AspisR1.OccupancyExpectedBridge.modelVariant variant))
              (fun k => AspisR1.ExtractedMaskQM31Exact.decode (get16 opened k)))[0]'(by simp [modelLanes, R0P.occupancyLanesLiteral]) =
              (AspisR1.ExtractedMaskQM31Exact.decode input + AspisR1.ExtractedMaskQM31Exact.decode output) *
                (AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨0, by decide⟩) *
                  (AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨0, by decide⟩) - 1)) := by
            simp [modelLanes, R0P.occupancyLanesLiteral]
          exact hm.trans (hinit.symm.trans hv'.symm)
        · by_cases h1 : i.val = 1
          · have hi : i = ⟨1, by decide⟩ := Fin.ext h1
            subst i
            have hv := hloopValues ⟨1, by decide⟩
            have hv' : AspisR1.ExtractedMaskQM31Exact.decode
                (AspisR1.OccupancyLiteralLoop.cellAt loopOut 1) =
                AspisR1.ExtractedMaskQM31Exact.decode
                  (AspisR1.OccupancyLiteralLoop.cellAt initial 1) := by simpa using hv
            have hinit : AspisR1.ExtractedMaskQM31Exact.decode
                (AspisR1.OccupancyLiteralLoop.cellAt initial 1) =
                (AspisR1.ExtractedMaskQM31Exact.decode input +
                  AspisR1.ExtractedMaskQM31Exact.decode output) *
                  (AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨9, by decide⟩) *
                      AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨1, by decide⟩) -
                    AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨0, by decide⟩)) := by
              rw [← get12_eq_cellAt initial ⟨1, by decide⟩]
              exact hcell1'
            have hm : (modelLanes
                (AspisR1.ExtractedMaskQM31Exact.decode input)
                (AspisR1.ExtractedMaskQM31Exact.decode output)
                (R0P.occupancyExpected (AspisR1.OccupancyExpectedBridge.modelVariant variant))
                (fun k => AspisR1.ExtractedMaskQM31Exact.decode (get16 opened k)))[1]'(by simp [modelLanes, R0P.occupancyLanesLiteral]) =
                (AspisR1.ExtractedMaskQM31Exact.decode input + AspisR1.ExtractedMaskQM31Exact.decode output) *
                  (AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨9, by decide⟩) *
                      AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨1, by decide⟩) -
                    AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨0, by decide⟩)) := by
              simp [modelLanes, R0P.occupancyLanesLiteral]
            exact hm.trans (hinit.symm.trans hv'.symm)
          · by_cases h2 : i.val = 2
            · have hi : i = ⟨2, by decide⟩ := Fin.ext h2
              subst i
              have hv := hloopValues ⟨2, by decide⟩
              have hv' : AspisR1.ExtractedMaskQM31Exact.decode
                  (AspisR1.OccupancyLiteralLoop.cellAt loopOut 2) =
                  AspisR1.ExtractedMaskQM31Exact.decode
                    (AspisR1.OccupancyLiteralLoop.cellAt initial 2) := by simpa using hv
              have hinit : AspisR1.ExtractedMaskQM31Exact.decode
                  (AspisR1.OccupancyLiteralLoop.cellAt initial 2) =
                  (AspisR1.ExtractedMaskQM31Exact.decode input +
                    AspisR1.ExtractedMaskQM31Exact.decode output) *
                    (AspisR1.ExtractedMaskQM31Exact.decode oneMinus *
                      AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨1, by decide⟩)) := by
                rw [← get12_eq_cellAt initial ⟨2, by decide⟩]
                exact hcell2'
              have hm : (modelLanes
                  (AspisR1.ExtractedMaskQM31Exact.decode input)
                  (AspisR1.ExtractedMaskQM31Exact.decode output)
                  (R0P.occupancyExpected (AspisR1.OccupancyExpectedBridge.modelVariant variant))
                  (fun k => AspisR1.ExtractedMaskQM31Exact.decode (get16 opened k)))[2]'(by simp [modelLanes, R0P.occupancyLanesLiteral]) =
                  (AspisR1.ExtractedMaskQM31Exact.decode input + AspisR1.ExtractedMaskQM31Exact.decode output) *
                    (AspisR1.ExtractedMaskQM31Exact.decode oneMinus *
                      AspisR1.ExtractedMaskQM31Exact.decode (get16 opened ⟨1, by decide⟩)) := by
                simp [modelLanes, R0P.occupancyLanesLiteral, hbothValue,
                  honeMinusValue', hoccupiedGet']
              exact hm.trans (hinit.symm.trans hv'.symm)
            · have hlow : 3 ≤ i.val := by omega
              have hhi : i.val < 11 := by omega
              have hv := hloopValues i
              have hv' : AspisR1.ExtractedMaskQM31Exact.decode
                  (AspisR1.OccupancyLiteralLoop.cellAt loopOut i.val) =
                  AspisR1.OccupancyLiteralLoop.laneValue opened oneMinus both i.val := by
                simpa only [if_pos (by omega : 3 ≤ i.val ∧ i.val < 11)] using hv
              have hm : (modelLanes
                  (AspisR1.ExtractedMaskQM31Exact.decode input)
                  (AspisR1.ExtractedMaskQM31Exact.decode output)
                  (R0P.occupancyExpected (AspisR1.OccupancyExpectedBridge.modelVariant variant))
                  (fun k => AspisR1.ExtractedMaskQM31Exact.decode (get16 opened k)))[i.val]'(by
                    have hlen : (modelLanes
                        (AspisR1.ExtractedMaskQM31Exact.decode input)
                        (AspisR1.ExtractedMaskQM31Exact.decode output)
                        (R0P.occupancyExpected (AspisR1.OccupancyExpectedBridge.modelVariant variant))
                        (fun k => AspisR1.ExtractedMaskQM31Exact.decode (get16 opened k))).length = 12 := by
                      simp [modelLanes, R0P.occupancyLanesLiteral]
                    omega) = AspisR1.OccupancyLiteralLoop.laneValue opened oneMinus both i.val := by
                have hidx : 2 + (i.val - (1 + 1 + 1)) = i.val - 1 := by omega
                have hopened : AspisR1.OccupancyLiteralLoop.openedCell opened (i.val - 1) =
                    get16 opened ⟨i.val - 1, by omega⟩ :=
                  openedCell_eq_get16 opened ⟨i.val - 1, by omega⟩
                unfold modelLanes
                unfold R0P.occupancyLanesLiteral
                rw [List.getElem_append_left (by
                  simpa only [List.length_append, List.length_cons, List.length_nil,
                    List.length_ofFn] using hhi)]
                rw [List.getElem_append_right (by
                  simpa only [List.length_cons, List.length_nil] using hlow)]
                rw [List.getElem_ofFn]
                simp only [List.length_cons, List.length_nil, Nat.zero_add]
                unfold AspisR1.OccupancyLiteralLoop.laneValue
                change (AspisR1.ExtractedMaskQM31Exact.decode input +
                    AspisR1.ExtractedMaskQM31Exact.decode output) *
                    ((1 - AspisR1.ExtractedMaskQM31Exact.decode
                        (get16 opened ⟨0, by decide⟩)) *
                      AspisR1.ExtractedMaskQM31Exact.decode
                        (get16 opened ⟨2 + (i.val - (1 + 1 + 1)), by omega⟩)) =
                  AspisR1.ExtractedMaskQM31Exact.decode both *
                    (AspisR1.ExtractedMaskQM31Exact.decode oneMinus *
                      AspisR1.ExtractedMaskQM31Exact.decode
                        (AspisR1.OccupancyLiteralLoop.openedCell opened (i.val - 1)))
                have hfin : (⟨2 + (i.val - (1 + 1 + 1)), by omega⟩ : Fin 16) =
                    ⟨i.val - 1, by omega⟩ := Fin.ext hidx
                rw [hfin, hopened, honeMinusValue', hoccupiedGet', hbothValue]
              exact hm.trans hv'.symm
      calc
        AspisR1.ExtractedMaskQM31Exact.decode (get12 out i) =
            AspisR1.ExtractedMaskQM31Exact.decode (get12 loopOut i) :=
          congrArg AspisR1.ExtractedMaskQM31Exact.decode hunchanged
        _ = AspisR1.ExtractedMaskQM31Exact.decode
            (AspisR1.OccupancyLiteralLoop.cellAt loopOut i.val) :=
          congrArg AspisR1.ExtractedMaskQM31Exact.decode (get12_eq_cellAt loopOut i)
        _ = _ := hmodel.symm
  have hcellsRaw : ∀ i : Fin 12,
      AspisR1.ExtractedMaskQM31Exact.decode
        (out.val[i.val]'(by simpa [out.property] using i.isLt)) =
      (R0P.occupancyLanesLiteral
          (AspisR1.ExtractedMaskQM31Exact.decode input)
          (AspisR1.ExtractedMaskQM31Exact.decode output)
          (R0P.occupancyExpected (AspisR1.OccupancyExpectedBridge.modelVariant variant))
          (fun k => AspisR1.ExtractedMaskQM31Exact.decode (get16 opened k)))[i.val]'(by
            have hlen : (R0P.occupancyLanesLiteral
                (AspisR1.ExtractedMaskQM31Exact.decode input)
                (AspisR1.ExtractedMaskQM31Exact.decode output)
                (R0P.occupancyExpected (AspisR1.OccupancyExpectedBridge.modelVariant variant))
                (fun k => AspisR1.ExtractedMaskQM31Exact.decode (get16 opened k))).length = 12 := by
              simp [R0P.occupancyLanesLiteral]
            omega) := by
    intro i
    simpa [get12, modelLanes] using hcells i
  have hlist := AspisR1.OccupancyVectorBridge.cells_to_model_list
    out (AspisR1.ExtractedMaskQM31Exact.decode input)
    (AspisR1.ExtractedMaskQM31Exact.decode output)
    (R0P.occupancyExpected (AspisR1.OccupancyExpectedBridge.modelVariant variant))
    (fun i => AspisR1.ExtractedMaskQM31Exact.decode (get16 opened i)) hcellsRaw
  change List.ofFn (fun i : Fin 12 => AspisR1.ExtractedMaskQM31Exact.decode
      (out.val[i.val]'(by simpa [out.property] using i.isLt))) =
    R0P.occupancyLanesLiteral
      (AspisR1.ExtractedMaskQM31Exact.decode input)
      (AspisR1.ExtractedMaskQM31Exact.decode output)
      (R0P.occupancyExpected (AspisR1.OccupancyExpectedBridge.modelVariant variant))
      (fun i => AspisR1.ExtractedMaskQM31Exact.decode (get16 opened i)) at hlist
  simpa [cellVector, modelLanes] using hlist

#print axioms generated_eq_run
#print axioms AspisR1.OccupancyLiteralExecutionAll12ExactListPublic.literal_success

end
end AspisR1.OccupancyLiteralExecutionAll12ExactListPublic
