import NMP_ObservedStep0
import NMP_ObservedStep1
import NMP_ObservedStep2
import NMP_ObservedStep3
import NMP_ObservedStep4
import NMP_ObservedStep5
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ObservedSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
/-- Exact full-Result source-order fold. This is emitted-body support, not a
physical RowSpec or a replacement for the SAME-argument child installations. -/
theorem emitted {H W : Type} (c : Calls) (s : Parent H W) :
 erase (body c s) = observed c s := by
 unfold body observed NMP_prepare.r1_semantic.verify_observed
 simp only [execute,step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.result_right,bind_tc_ok,bind_tc_fail,bind_tc_div,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame]
 repeat' first
 | rfl
 | (apply NMT_CallTree.result_congr; intro x; simp only [execute,step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.result_right,bind_tc_ok,bind_tc_fail,bind_tc_div,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame])
 | (split <;> simp only [execute,step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.result_right,bind_tc_ok,bind_tc_fail,bind_tc_div,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame])
#print axioms emitted
end AspisR1.NMP_ObservedSteps
