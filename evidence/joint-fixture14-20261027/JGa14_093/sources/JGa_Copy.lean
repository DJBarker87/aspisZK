import JGa_CopyLoop
import JGa_CopyPatterns
import JGa_ActiveLoop
import JFy_CopyResidual
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_Copy
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal

theorem source (a : Array field.QM31 16#usize) (h1 : field.QM31) (s : Selectors)
    (lambda chi : field.QM31) (index : U64) (v : PoolV1PairForestCompiledVariantV1)
    (ha : canonical a) (hh1 : Canon h1) (hh : canonical s.high) (hl : canonical s.low)
    (hlam : Canon lambda) (hchi : Canon chi) :
    ∃ out,evaluate_with_selectors a h1 s lambda chi index v=ok out ∧ Canon out.residual ∧ Canon out.active := by
  obtain ⟨patterns,hp,hpc⟩ := WP.spec_imp_exists (JGa_CopyPatterns.source a lambda ha hlam)
  have hz := JFy_ZeroArrays.source 2#usize
  obtain ⟨pv,pw,cv,cw,hloop,hpv,hpw,hcv,hcw⟩ := JGa_CopyLoop.source 136 0#usize s index v patterns _ _ _ _ rfl hh hl hpc hz hz hz hz
  obtain ⟨active,hactive,hac⟩ := WP.spec_imp_exists (JGa_ActiveLoop.full s hh hl)
  obtain ⟨res,hr,hrc⟩ := JFy_CopyResidual.source ⟨pv,pw,cv,cw⟩ h1 chi hpv hcv hpw hcw hh1 hchi
  obtain ⟨out,ho,hoc,_⟩ := JFy_FieldTotal.mul active res hac hrc
  refine ⟨⟨out,active⟩,?_,hoc,hac⟩
  unfold evaluate_with_selectors
  dsimp only
  rw [hp,bind_tc_ok,hloop,bind_tc_ok]
  change (do let active ← Selectors.active s;let r ← copy_residual ⟨pv,pw,cv,cw⟩ h1 chi;let q ← field.QM31.mul active r;ok {residual:=q,active})=ok {residual:=out,active}
  rw [hactive,bind_tc_ok,hr,bind_tc_ok,ho,bind_tc_ok]
#print axioms source
end AspisR1.JGa_Copy
end
