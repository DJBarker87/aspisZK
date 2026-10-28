import RPv_JFy_PreparedSteps
import NDO_JFy_BoundedCanonical
import RPu_FIq_Native10
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_InitialBuilder
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open JFy_PreparedSteps (Valid)
open pool_v1.pair_forest_semantic_terminal

 theorem cell (pr pf : field.PreparedQm31Multiplier) (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (i : Usize) (hi : i.val<16) (hr : Valid pr) (hf : Valid pf) (ho : canonical o.z) :
    ∃ q,semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut (pr,o,pf) i=ok (q,(pr,o,pf)) ∧ Canon q := by
  have spec : semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut (pr,o,pf) i
      ⦃ out => out.2=(pr,o,pf) ∧ Canon out.1 ⦄ := by
    unfold semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    step* <;> first | assumption | scalar_tac
  obtain ⟨⟨q,last⟩,call,same,hq⟩ := WP.spec_imp_exists spec
  exact ⟨q,same ▸ call,hq⟩
#print axioms cell

@[step] theorem source (pr pf : field.PreparedQm31Multiplier) (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (hr : Valid pr) (hf : Valid pf) (ho : canonical o.z) :
    array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO (pr,o,pf)
      ⦃ out => canonical out ⦄ := by
  apply exists_imp_spec
  unfold array_from_fn_copy
  apply JFy_BoundedCanonical.source
  intro i hi
  exact cell pr pf o i hi hr hf ho
#print axioms source
end AspisR1.JFy_InitialBuilder
end
