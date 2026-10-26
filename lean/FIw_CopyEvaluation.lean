import FIw_CopyTransport
import FIq_Native14
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_CopyEvaluation
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev Variant := pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1
abbrev Copy := pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1

theorem value (openings : Array NQ 16#usize) (h : NQ) (selectors : Selectors)
    (lambda chi : NQ) (index : U64) (variant : Variant) (copy : Copy)
    (run : pool_v1.pair_forest_copy_terminal.evaluate_with_selectors openings h selectors
      lambda chi index variant=ok copy) :
    ∃ (patterns : Array NQ 14#usize) (pv pw cv cw : Array NQ 2#usize),
      pool_v1.pair_forest_copy_terminal.pattern_values openings lambda=ok patterns ∧
      pool_v1.pair_forest_copy_terminal.evaluate_with_selectors_loop selectors index variant patterns
        (Array.repeat 2#usize field.QM31.ZERO) (Array.repeat 2#usize field.QM31.ZERO)
        (Array.repeat 2#usize field.QM31.ZERO) (Array.repeat 2#usize field.QM31.ZERO) 0#usize=
          ok (pv,pw,cv,cw) ∧
      pool_v1.pair_forest_copy_terminal.Selectors.active selectors=ok copy.active ∧
      ((∀ x∈pv.val,Canon x) → (∀ x∈pw.val,Canon x) →
       (∀ x∈cv.val,Canon x) → (∀ x∈cw.val,Canon x) →
       Canon h → Canon chi → Canon copy.active →
       Canon copy.residual ∧ decode copy.residual=decode copy.active*
         R0P.copyResidual (FIw_CopyTransport.row ⟨pv,pw,cv,cw⟩) (decode h) (decode chi)) := by
  unfold pool_v1.pair_forest_copy_terminal.evaluate_with_selectors at run
  obtain ⟨patterns,hp,r1⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨⟨pv,pw,cv,cw⟩,hl,r2⟩ := FIv_Map.bind_success _ _ _ r1
  obtain ⟨active,ha,r3⟩ := FIv_Map.bind_success _ _ _ r2
  obtain ⟨residual,hr,r4⟩ := FIv_Map.bind_success _ _ _ r3
  obtain ⟨out,ho,r5⟩ := FIv_Map.bind_success _ _ _ r4
  have same := Result.ok.inj r5
  cases same
  refine ⟨patterns,pv,pw,cv,cw,hp,hl,ha,?_⟩
  intro hpv hpw hcv hcw hh hc hac
  have vr := FIw_CopyMeaning.value_exact ⟨pv,pw,cv,cw⟩ h chi residual hpv hcv hpw hcw hh hc hr
  have vo := FIv_NativeValue.mul active residual out hac vr.1 ho
  exact ⟨vo.1,by rw [vo.2,vr.2,FIw_CopyTransport.value_exact]⟩
#print axioms value
end AspisR1.FIw_CopyEvaluation
end
