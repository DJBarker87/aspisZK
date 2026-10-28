import NDO_JGa_SemanticTail
import NDO_JFy_SemanticValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_Semantic
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)
open JFy_PublicCanonical (p)

theorem source (a b c : Array field.QM31 16#usize)
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (ha : canonical a)
    (hb : canonical b) (hc : canonical c) (hh : canonical s.high) (hl : canonical s.low) :
    ∃ out,pool_v1.pair_forest_semantic_terminal.semantic_packed p ⟨a,b,c⟩ s=ok out ∧
      canonical out ∧ decoded out=FIy_NativeCoefficients.model p ⟨a,b,c⟩ s := by
  obtain ⟨schedule,path,hs,hsc,hp,hpc,hsem⟩ := JFy_SemanticPrefix.source ⟨a,b,c⟩ s ha hb hh hl
  obtain ⟨out,ho,hoc⟩ := JGa_SemanticTail.source ⟨a,b,c⟩ s path ha hb hc hh hl hpc
  have call := hsem.trans ho
  exact ⟨out,call,hoc,(JFy_SemanticValue.value a b c s out ha hb hc hh hl call).2⟩
#print axioms source
end AspisR1.JGa_Semantic
end
