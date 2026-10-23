import ScheduleEnclosingBridge
import SchedulePacking
import ScheduleFamilyFieldTransport

/-! The complete actual schedule caller contributes its32 retained residuals
to all24 packed cells, after the already-proved exact field embedding. -/
set_option autoImplicit false
namespace AspisR1.ScheduleCompletePacking
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQmPackBase4Semantic
open AspisR1.ValueLaneSourceVector
open AspisR1.ValueLaneResidualList
open AspisR1.ValueFamilyFieldTransport
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev exactOpenings := AspisR1.ScheduleProgram.exactOpenings
abbrev pointSelector := AspisR1.ScheduleProgram.pointSelector
abbrev modelVariant := AspisR1.ScheduleProgram.modelVariant
abbrev exactCell := AspisR1.AbsorptionCallback.sourceCell
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode

theorem mapped_initial_list {K L : Type} [Field K] [Field L]
    (g : K →+* L) (v : R0P.Variant) (o : R0P.Openings K) (sel : R0P.Sel K) :
    (List.ofFn (R0P.scheduleInitial v o sel)).map g =
      List.ofFn (R0P.scheduleInitial v (mapOpenings g o) (fun i => g (sel i))) := by
  rw [List.map_ofFn]
  exact congrArg List.ofFn (funext (fun i => AspisR1.ScheduleFamilyFieldTransport.map_initial g v o sel i))

theorem mapped_absorption_list {K L : Type} [Field K] [Field L]
    (g : K →+* L) (v : R0P.Variant) (o : R0P.Openings K) (sel : R0P.Sel K) :
    (List.ofFn (R0P.scheduleAbsorption v o sel)).map g =
      List.ofFn (R0P.scheduleAbsorption v (mapOpenings g o) (fun i => g (sel i))) := by
  rw [List.map_ofFn]
  exact congrArg List.ofFn (funext (fun i => AspisR1.ScheduleFamilyFieldTransport.map_absorption g v o sel i))

theorem arrayVector_list_map (a : Array QM 16#usize) :
    List.ofFn (arrayVector a) =
      (List.ofFn (fun i : Fin 16 => decode (exactCell a i))).map f := by
  rw [List.map_ofFn]
  rfl

theorem arrays_to_wide_family
    (initial absorption : Array QM 16#usize)
    (v : R0P.Variant) (o : R0P.Openings AspisV8R15.ExactTowerBase.QM31Exact)
    (sel : R0P.Sel AspisV8R15.ExactTowerBase.QM31Exact) (pub : R0P.Public Wide)
    (hv : pub.variant = v)
    (hi : ∀ i : Fin 16, decode (exactCell initial i) = R0P.scheduleInitial v o sel i)
    (ha : ∀ i : Fin 16, decode (exactCell absorption i) = R0P.scheduleAbsorption v o sel i) :
    List.ofFn (arrayVector initial) ++ List.ofFn (arrayVector absorption) =
      (R0P.scheduleFamily (K := Wide)).residuals pub (mapOpenings f o) (fun i => f (sel i)) := by
  have hiFn : (fun i : Fin 16 => decode (exactCell initial i)) = R0P.scheduleInitial v o sel := funext hi
  have haFn : (fun i : Fin 16 => decode (exactCell absorption i)) = R0P.scheduleAbsorption v o sel := funext ha
  rw [arrayVector_list_map, arrayVector_list_map, hiFn, haFn]
  have hInitial := mapped_initial_list f v o sel
  have hAbsorption := mapped_absorption_list f v o sel
  have hBoth := congrArg₂ (fun a b : List Wide => a ++ b) hInitial hAbsorption
  simpa only [R0P.scheduleFamily, hv] using hBoth

def run (packed : Array QM 24#usize) (public1 : Public) (openings : Openings) (selectors : Selectors) :
    Result (Array QM 24#usize) := do
  let (initial, absorption) ← AspisR1ScheduleEnclosingCandidate.pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption
    public1 openings selectors
  AspisR1.SchedulePacking.run packed initial absorption

theorem enclosing_eq_run (packed : Array QM 24#usize) (public1 : Public) (openings : Openings) (selectors : Selectors) :
    AspisR1ScheduleEnclosingCandidate.pool_v1.pair_forest_semantic_terminal.add_schedule_lanes
      packed public1 openings selectors = run packed public1 openings selectors := by
  unfold AspisR1ScheduleEnclosingCandidate.pool_v1.pair_forest_semantic_terminal.add_schedule_lanes
    run AspisR1.SchedulePacking.run
  simp only [bind_assoc]

theorem actual_enclosing_scheduleFamily (point : Array QM 10#usize) (selectors : Selectors)
    (packed : Array QM 24#usize) (public1 : Public) (openings : Openings) (pub : R0P.Public Wide)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hp : CanonicalArray packed) (hz : CanonicalArray openings.z)
    (hv : pub.variant = modelVariant public1.variant) :
    ∃ out, AspisR1ScheduleEnclosingCandidate.pool_v1.pair_forest_semantic_terminal.add_schedule_lanes
      packed public1 openings selectors = .ok out ∧ CanonicalArray out ∧
      ∀ j : Fin 24, f (decoded out j) = f (decoded packed j) +
        R0P.pack4 PackB (fun k : Fin 4 => selectList 0
          ((R0P.scheduleFamily (K := Wide)).residuals pub
            (mapOpenings f (exactOpenings openings)) (fun i => f (pointSelector point i))) (4*j.val+k.val)) := by
  obtain ⟨initial, absorption, hsource, hci, hca, hvi, hva⟩ :=
    AspisR1.ScheduleEnclosingBridge.actual_schedule_arrays point selectors public1 openings hpoint hbox hz
  have hciArray : CanonicalArray initial := by
    intro i
    exact hci ⟨i.val, by simpa using i.isLt⟩
  have hcaArray : CanonicalArray absorption := by
    intro i
    exact hca ⟨i.val, by simpa using i.isLt⟩
  have hlist := arrays_to_wide_family initial absorption (modelVariant public1.variant)
    (exactOpenings openings) (pointSelector point) pub hv hvi hva
  obtain ⟨out, hpack, hcout, hvout⟩ := AspisR1.SchedulePacking.run_source_list packed initial absorption hp hciArray hcaArray
  refine ⟨out, ?_, hcout, ?_⟩
  · rw [enclosing_eq_run]
    simp only [run, hsource, bind_tc_ok, Aeneas.Std.uncurry_apply_pair, hpack]
  · simpa only [hlist] using hvout

#print axioms mapped_initial_list
#print axioms mapped_absorption_list
#print axioms arrayVector_list_map
#print axioms arrays_to_wide_family
#print axioms enclosing_eq_run
#print axioms actual_enclosing_scheduleFamily
end
end AspisR1.ScheduleCompletePacking
