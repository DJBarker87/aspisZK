import FIx_Builder
import FIx_HighSumInner
import FIw_WordValue
import FIq_Native09
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_PreweightedSelect
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
abbrev call := @pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut

def selected {N : Usize} (a : Array NQ N) (start group lane : Nat) : K :=
  if start≤4*group+lane ∧ 4*group+lane<start+N.val then
    FIv_NativeArray.value a (4*group+lane-start) else 0

theorem value {N : Usize} (a : Array NQ N) (start group lane : Usize) (result : NQ)
    (last : pool_v1.pair_forest_semantic_terminal.add_preweighted.closure N)
    (hc : ∀ x∈a.val,Canon x)
    (run : call (group,start,a) lane=ok (result,last)) :
    Canon result ∧ decode result=selected a start.val group.val lane.val ∧ last=(group,start,a) := by
  unfold call pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut at run
  obtain ⟨base,hbase,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨source,hsource,run⟩ := FIv_Map.bind_success _ _ _ run
  have vb := FIw_WordValue.mul 4#usize group base hbase
  have vs := FIw_WordValue.add base lane source hsource
  have sourceValue : source.val=4*group.val+lane.val := by
    rw [vs,vb]
    rfl
  split at run
  · rename_i above
    obtain ⟨limit,hlimit,run⟩ := FIv_Map.bind_success _ _ _ run
    have vl := FIw_WordValue.add start N limit hlimit
    split at run
    · rename_i below
      obtain ⟨offset,hoffset,run⟩ := FIv_Map.bind_success _ _ _ run
      obtain ⟨cell,hcell,run⟩ := FIv_Map.bind_success _ _ _ run
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj run)
      have off : offset.val=source.val-start.val := by
        obtain ⟨z,hz,hvalue⟩ := WP.spec_imp_exists (UScalar.sub_spec (x := source) (y := start) (by exact above))
        have same := Result.ok.inj (hoffset.symm.trans hz)
        subst z
        exact hvalue
      have canon := FIv_NativeArray.canonical a offset cell hc hcell
      refine ⟨canon,?_,rfl⟩
      have inside : start.val≤4*group.val+lane.val ∧ 4*group.val+lane.val<start.val+N.val := by
        have hab : start.val≤source.val := above
        have hbl : source.val<limit.val := below
        rw [vl] at hbl
        rw [sourceValue] at hab hbl
        exact ⟨hab,hbl⟩
      rw [selected,if_pos inside,←FIv_NativeArray.read a offset cell hcell,off,sourceValue]
    · rename_i below
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj run)
      refine ⟨FIv_NativeValue.zero.1,?_,rfl⟩
      rw [FIv_NativeValue.zero.2,selected,if_neg]
      intro h
      apply below
      change source.val<limit.val
      rw [vl,sourceValue]
      exact h.2
  · rename_i above
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj run)
    refine ⟨FIv_NativeValue.zero.1,?_,rfl⟩
    rw [FIv_NativeValue.zero.2,selected,if_neg]
    intro h
    apply above
    change start.val≤source.val
    rw [sourceValue]
    exact h.1
#print axioms value
end AspisR1.FIx_PreweightedSelect
end
