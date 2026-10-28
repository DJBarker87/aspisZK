import NDO_JGb_Horner
import NDO_JGb_Challenges
import NDO_JGa_CopyFixture
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGb_CompositionSuffix
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

/-- The suffix consumes the very semantic/copy results obtained above, rather
than selecting fresh operands for the Horner folds. -/
def run (selected : Array field.QM31 84#usize) (a : Array field.QM31 16#usize)
    (mask : Array field.QM31 10#usize) (sem : Array field.QM31 24#usize)
    (pos : Array field.QM31 4#usize) (h1 : field.QM31)
    (copy : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1) := do
  let comp ← JGb_Horner.run sem pos JFu_TerminalPrefix.challenges.theta copy.residual
  let i ← SELECTED_G_COLUMN
  let g ← selected_claim selected 0#usize i
  ok (.Ok (comp,a,mask,g,h1,copy.active) : core.result.Result _ PoolV1PairForestSemanticTerminalErrorV1)

theorem source (selected : Array field.QM31 84#usize) (a : Array field.QM31 16#usize)
    (mask : Array field.QM31 10#usize) (sem : Array field.QM31 24#usize)
    (pos : Array field.QM31 4#usize) (h1 : field.QM31)
    (copy : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1)
    (hselected : canonical selected) (hsem : canonical sem) (hpos : canonical pos)
    (hc : Canon copy.residual) :
    ∃ comp g,run selected a mask sem pos h1 copy=ok (.Ok (comp,a,mask,g,h1,copy.active)) ∧
      Canon comp ∧ Canon g ∧
      decode comp=FIv_CompositionValue.polynomial
        (decode JFu_TerminalPrefix.challenges.theta) sem pos copy.residual := by
  obtain ⟨comp,hcomp,hcc,hcv⟩ := JGb_Horner.source sem pos _ _ JGb_Challenges.theta hc hsem hpos
  obtain ⟨g,hg,hgc⟩ := JFy_SelectedRead.source selected hselected 0#usize 27#usize (by decide) (by decide)
  refine ⟨comp,g,?_,hcc,hgc,hcv⟩
  unfold run
  rw [hcomp,bind_tc_ok]
  have col : SELECTED_G_COLUMN=ok 27#usize := by
    unfold SELECTED_G_COLUMN SELECTED_H1_COLUMN POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
      state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
    have spec : (do let i ← (16#usize+10#usize : Result Usize);i+1#usize) ⦃ out => out.val=27 ⦄ := by
      step* <;> scalar_tac
    obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
    have same : out=27#usize := UScalar.eq_of_val_eq value
    exact same ▸ call
  rw [col,bind_tc_ok]
  change (do let g ← selected_claim selected 0#usize 27#usize
             ok (core.result.Result.Ok (comp,a,mask,g,h1,copy.active) : core.result.Result _ PoolV1PairForestSemanticTerminalErrorV1))=_
  rw [hg,bind_tc_ok]
#print axioms source
end AspisR1.JGb_CompositionSuffix
end
