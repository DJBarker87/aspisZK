import RPu_FIy_MapValue
import RPu_FIy_FrontierMeaning
import RPu_FIx_ArrayMeaning
import RPu_FIq_Native09
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_ValueSelector
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIy_FrontierStep (Selectors)
abbrev call := pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
abbrev callback := pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31

theorem cell (s : Selectors) (index : Usize) (out : NQ) (last : Selectors)
    (hh : canonical s.high) (hl : canonical s.low) (success : call s index=ok (out,last)) :
    Canon out ∧ decode out=FIy_FrontierMeaning.rowValue s (1008+index.val) ∧ last=s := by
  unfold call pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut at success
  obtain ⟨base,hbase,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨row,hrow,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨v,hv,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨eq,eqLast⟩ := Prod.mk.inj (Result.ok.inj success)
  subst last
  subst v
  have bv := FIw_WordValue.mul 16#usize pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK base hbase
  rw [pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK] at bv
  change base.val=1008 at bv
  have rv := FIw_WordValue.add base index row hrow
  have v := FIw_SelectorRow.value_exact s row out hh hl hv
  refine ⟨v.1,?_,rfl⟩
  rw [v.2,rv,bv]
  rfl

def model (s : Selectors) (i : Fin (3#usize).val) : K := FIy_FrontierMeaning.rowValue s (1008+2*i.val)

theorem value (s : Selectors) (out : Array NQ 3#usize)
    (hh : canonical s.high) (hl : canonical s.low)
    (success : FIq_Native.core.array.Array.map callback (Array.make 3#usize [0#usize,2#usize,4#usize]) s=ok out) :
    canonical out ∧ decoded out=model s := by
  have v := FIy_MapValue.value callback Canon decode (fun i : Usize=>FIy_FrontierMeaning.rowValue s (1008+i.val))
    (Array.make 3#usize [0#usize,2#usize,4#usize]) s out
    (by intro i _ y c h;exact cell s i y c hh hl h) success
  refine ⟨v.1,?_⟩
  apply FIx_ArrayMeaning.decoded_of_map
  rw [v.2]
  rfl
#print axioms cell
#print axioms value
end AspisR1.FIy_ValueSelector
end
