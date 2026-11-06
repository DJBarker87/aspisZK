import NJX_PatternPacket
import NJX_PatternModel
import RPv_FJk_PatternValues
import RPv_JGa_CopyPatterns
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_PatternAssociation
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJX_PatternPacket (atoms starts)
theorem atoms_value (lambda : NQ) (o : Array NQ 16#usize) (w : Fin 4 → NQ)
 (hw : ∀ j,decode (w j)=(List.ofFn (fun i : Fin 8=>decode lambda^(i.val+1)*decode (NJL_WindowStep.opened o (starts j) i))).sum) :
 (fun k=>decode (atoms o w k))=NJX_PatternModel.atoms (FIw_ArrayValue.decoded o) (decode lambda) := by
 funext i
 unfold atoms NJX_PatternModel.atoms
 split
 · rfl
 · split
   · rw [hw]
     unfold NJX_PatternModel.window
     congr 2
   · exact NJX_PatternPacket.constant_value

/-- Full adopted literal Result and canonical14array, for association with
windowed native output by canonical injectivity at identical arguments. -/
theorem cohort (lambda : NQ) (o : Array NQ 16#usize) (hl : Canon lambda)
 (ho : FIw_ArrayValue.canonical o) :
 ∃ out,FIq_Native.pool_v1.pair_forest_copy_terminal.pattern_values o lambda=ok out ∧
 FIw_ArrayValue.canonical out ∧
 FIw_ArrayValue.decoded out=R0P.copyPatternValuesLiteral (FIw_ArrayValue.decoded o) (decode lambda) := by
 obtain ⟨out,run,_⟩ := WP.spec_imp_exists (JGa_CopyPatterns.source o lambda ho hl)
 exact ⟨out,run,FJk_PatternValues.value o lambda out ho hl run⟩
#print atoms_value
#print cohort
#print axioms atoms_value
#print axioms cohort
end AspisR1.NJX_PatternAssociation
end
