import NDO_FIv_FoldsTotal
import NDO_JFy_SelectedRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermHorner
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal
abbrev Copy := pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1

def run (claims : Array NQ 84#usize) (z : Array NQ 16#usize) (mask : Array NQ 10#usize)
 (semantic : Array NQ 24#usize) (poseidon : Array NQ 4#usize) (theta h1 : NQ) (copy : Copy) := do
 let comp←FIv_FoldsTotal.body semantic poseidon theta copy.residual
 let col←SELECTED_G_COLUMN
 let g←selected_claim claims 0#usize col
 ok (comp,z,mask,g,h1,copy.active)

theorem column : SELECTED_G_COLUMN=ok 27#usize := by
 unfold SELECTED_G_COLUMN SELECTED_H1_COLUMN POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
 have spec : (do let i←(16#usize+10#usize : Result Usize);i+1#usize) ⦃out=>out.val=27⦄ := by
  step* <;> scalar_tac
 obtain ⟨out,call,value⟩:=WP.spec_imp_exists spec
 have same : out=27#usize := UScalar.eq_of_val_eq value
 exact same ▸ call

/--237's complete24+4 Horner suffix on its actual states. The finite-fold
induction is inherited unchanged; no native whole-loop reduction is used.
All field domains and selected27 bounds are discharged from actual inputs. -/
theorem source (claims : Array NQ 84#usize) (z : Array NQ 16#usize) (mask : Array NQ 10#usize)
 (semantic : Array NQ 24#usize) (poseidon : Array NQ 4#usize) (theta h1 : NQ) (copy : Copy)
 (hc : canonical claims) (hs : canonical semantic) (hp : canonical poseidon)
 (ht : Canon theta) (hr : Canon copy.residual) :
 ∃ comp g,run claims z mask semantic poseidon theta h1 copy=ok (comp,z,mask,g,h1,copy.active) ∧
 Canon comp ∧ Canon g ∧ decode comp=FIv_CompositionValue.polynomial (decode theta) semantic poseidon copy.residual := by
 obtain ⟨comp,call,cc,value⟩:=FIv_FoldsTotal.value semantic poseidon theta copy.residual ht hr hs hp
 obtain ⟨g,gcall,cg⟩:=JFy_SelectedRead.source claims hc 0#usize 27#usize (by decide) (by decide)
 refine ⟨comp,g,?_,cc,cg,value⟩
 simp only [run,call,column,gcall,bind_tc_ok]
#print axioms column
#print source
#print axioms source
end AspisR1.NKR_TermHorner
end
