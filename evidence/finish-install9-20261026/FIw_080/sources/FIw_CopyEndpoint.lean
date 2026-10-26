import FIw_ArrayReadValue
import FIw_SelectorRow
import FIw_ScalarArithmetic
import FIw_CopyTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_CopyEndpoint
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
abbrev Endpoint := pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestEndpoint
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors

def modelSelectors (s : Selectors) : R0P.CopySelectors K where
  high := fun i=>FIv_NativeArray.value s.high i.val
  low := fun i=>FIv_NativeArray.value s.low i.val

def modelEndpoint (e : Endpoint) (hr : e.row.val<1024) (hs : e.slot.val<2)
    (hp : e.pattern.val<14) : R0P.CopyEndpoint :=
  ⟨⟨e.row.val,hr⟩,⟨e.slot.val,hs⟩,⟨e.pattern.val,hp⟩⟩

theorem value (values weights valuesOut weightsOut : Array NQ 2#usize)
    (e : Endpoint) (tag weight : U32) (patterns : Array NQ 14#usize) (s : Selectors)
    (hv : canonical values) (hw : canonical weights) (hp : canonical patterns)
    (hh : canonical s.high) (hl : canonical s.low)
    (hr : e.row.val<1024) (hs : e.slot.val<2) (hpat : e.pattern.val<14)
    (ht : tag.val<FIw_ScalarArithmetic.P)
    (run : pool_v1.pair_forest_copy_terminal.accumulate_endpoint
      values weights e tag weight patterns s=ok (valuesOut,weightsOut)) :
    canonical valuesOut ∧ canonical weightsOut ∧
      (decoded valuesOut,decoded weightsOut)=R0P.copyAccumulateEndpoint
        (decoded values) (decoded weights) (modelEndpoint e hr hs hpat)
        tag.val (weight.val : K) (decoded patterns) (modelSelectors s) := by
  unfold pool_v1.pair_forest_copy_terminal.accumulate_endpoint at run
  obtain ⟨rowIndex,h_rowIndex,r1⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨selector,h_selector,r2⟩ := FIv_Map.bind_success _ _ _ r1
  obtain ⟨slot,h_slot,r3⟩ := FIv_Map.bind_success _ _ _ r2
  obtain ⟨oldWeight,h_oldWeight,r4⟩ := FIv_Map.bind_success _ _ _ r3
  obtain ⟨weighted,h_weighted,r5⟩ := FIv_Map.bind_success _ _ _ r4
  obtain ⟨nextWeight,h_nextWeight,r6⟩ := FIv_Map.bind_success _ _ _ r5
  obtain ⟨newWeights,h_newWeights,r7⟩ := FIv_Map.bind_success _ _ _ r6
  obtain ⟨tagValue,h_tagValue,r8⟩ := FIv_Map.bind_success _ _ _ r7
  obtain ⟨patternIndex,h_patternIndex,r9⟩ := FIv_Map.bind_success _ _ _ r8
  obtain ⟨pattern,h_pattern,r10⟩ := FIv_Map.bind_success _ _ _ r9
  obtain ⟨compressed,h_compressed,r11⟩ := FIv_Map.bind_success _ _ _ r10
  obtain ⟨oldValue,h_oldValue,r12⟩ := FIv_Map.bind_success _ _ _ r11
  obtain ⟨selected,h_selected,r13⟩ := FIv_Map.bind_success _ _ _ r12
  obtain ⟨nextValue,h_nextValue,r14⟩ := FIv_Map.bind_success _ _ _ r13
  obtain ⟨newValues,h_newValues,r15⟩ := FIv_Map.bind_success _ _ _ r14
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj r15)
  have rowValue : rowIndex.val=e.row.val := by
    cases Result.ok.inj h_rowIndex
    exact core.convert.num.FromUsizeU16.from_val_eq e.row
  have slotValue : slot.val=e.slot.val := by
    cases Result.ok.inj h_slot
    exact core.convert.num.FromUsizeU8.from_val_eq e.slot
  have patternValue : patternIndex.val=e.pattern.val := by
    cases Result.ok.inj h_patternIndex
    exact core.convert.num.FromUsizeU8.from_val_eq e.pattern
  have slotBound : slot.val<(2#usize).val := by rw [slotValue];exact hs
  have patternBound : patternIndex.val<(14#usize).val := by rw [patternValue];exact hpat
  have sv := FIw_SelectorRow.value_exact s rowIndex selector hh hl h_selector
  have ow := FIv_NativeArray.canonical weights slot oldWeight hw h_oldWeight
  have ov := FIv_NativeArray.canonical values slot oldValue hv h_oldValue
  have pv := FIv_NativeArray.canonical patterns patternIndex pattern hp h_pattern
  have weightedV := FIw_ScalarArithmetic.mul selector weighted weight h_weighted
  have nextWeightV := FIv_NativeValue.add oldWeight weighted nextWeight ow weightedV.1 h_nextWeight
  have weightUpdate := FIw_ArrayValue.update weights newWeights slot nextWeight slotBound hw nextWeightV.1 h_newWeights
  change pool_v1.pair_forest_semantic_terminal.lift_m31 tag=ok tagValue at h_tagValue
  rw [FIw_ScalarArithmetic.lift_run] at h_tagValue
  cases Result.ok.inj h_tagValue
  have tagV := FIw_ScalarArithmetic.lift_value tag ht
  have compressedV := FIv_NativeValue.add _ pattern compressed tagV.1 pv h_compressed
  have selectedV := FIv_NativeValue.mul selector compressed selected sv.1 compressedV.1 h_selected
  have nextValueV := FIv_NativeValue.add oldValue selected nextValue ov selectedV.1 h_nextValue
  have valueUpdate := FIw_ArrayValue.update values newValues slot nextValue slotBound hv nextValueV.1 h_newValues
  refine ⟨valueUpdate.1,weightUpdate.1,?_⟩
  rw [valueUpdate.2,weightUpdate.2]
  rw [nextValueV.2,selectedV.2,compressedV.2,tagV.2,nextWeightV.2,weightedV.2,sv.2,
    FIw_ArrayReadValue.read values slot slotBound oldValue h_oldValue,
    FIw_ArrayReadValue.read weights slot slotBound oldWeight h_oldWeight,
    FIw_ArrayReadValue.read patterns patternIndex patternBound pattern h_pattern]
  simp only [R0P.copyAccumulateEndpoint,R0P.copySelectorRow,modelSelectors,modelEndpoint,
    slotValue,patternValue,rowValue]
#print axioms value
end AspisR1.FIw_CopyEndpoint
end
