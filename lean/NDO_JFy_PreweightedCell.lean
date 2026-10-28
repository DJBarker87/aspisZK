import RPv_JFy_Steps
import NDO_JFy_BoundedCanonical
import RPv_FIx_PreweightedSelect
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_PreweightedCell
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

theorem source {N : Usize} (a : Array field.QM31 N) (start group lane : Usize)
    (ha : canonical a) (bound : start.val+N.val≤96) (hg : group.val<24) (hl : lane.val<4) :
    ∃ q,add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut (group,start,a) lane=ok (q,(group,start,a)) ∧ Canon q := by
  have spec : add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut (group,start,a) lane
      ⦃ out => out.2=(group,start,a) ∧ Canon out.1 ⦄ := by
    unfold add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    step*
    all_goals first | assumption | scalar_tac | exact FIv_NativeValue.zero.1
  obtain ⟨⟨q,last⟩,call,same,hq⟩ := WP.spec_imp_exists spec
  exact ⟨q,same ▸ call,hq⟩
#print axioms source

theorem gather {N : Usize} (a : Array field.QM31 N) (start group : Usize)
    (ha : canonical a) (bound : start.val+N.val≤96) (hg : group.val<24) :
    ∃ lanes,array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy
      (add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 N) field.QM31.ZERO (group,start,a)=ok lanes ∧ canonical lanes := by
  unfold array_from_fn_copy
  apply JFy_BoundedCanonical.source
  intro lane hl
  exact source a start group lane ha bound hg hl
#print axioms gather
end AspisR1.JFy_PreweightedCell
end
