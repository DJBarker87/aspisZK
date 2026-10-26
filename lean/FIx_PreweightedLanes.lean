import FIx_PreweightedSelect
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_PreweightedLanes
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)

theorem value {N : Usize} (a : Array NQ N) (start group : Usize) (lanes : Array NQ 4#usize)
    (hc : ∀ x∈a.val,Canon x)
    (run : array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy
      (pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 N)
      field.QM31.ZERO (group,start,a)=ok lanes) :
    (∀ x∈lanes.val,Canon x) ∧ lanes.val.map decode=List.ofFn
      (fun i : Fin (4#usize).val=>FIx_PreweightedSelect.selected a start.val group.val i.val) := by
  unfold array_from_fn_copy at run
  apply FIx_Builder.fromFn (4#usize)
    (pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 N)
    Canon decode (fun i=>FIx_PreweightedSelect.selected a start.val group.val i) (group,start,a) lanes _ run
  intro i hi result last called
  exact FIx_PreweightedSelect.value a start group i result last hc called
#print axioms value
end AspisR1.FIx_PreweightedLanes
end
