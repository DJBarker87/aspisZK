import NHG_ExtraLeaves
import NJB_ArrayCarrier
import NDO_JGa_EmptyRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_AppendDomains
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
abbrev D := Array U32 8#usize
abbrev Frontier := Array D 20#usize
abbrev High := Array NQ 64#usize

def level (i : Fin 20) : Usize := UScalar.ofNatCore .Usize i.val (by scalar_tac)
def frontier (f : Frontier) (i : Fin 20) : D := NJB_ArrayCarrier.cell f ⟨i.val,by have h:=i.isLt;scalar_tac⟩
def high (s : High) (i : Fin 20) : NQ := NJB_ArrayCarrier.cell s ⟨34+i.val,by have h:=i.isLt;scalar_tac⟩

theorem level_value (i : Fin 20) : (level i).val=i.val := rfl
/-- SAME actual source frontier[level], high[34+level], all20levels;
these are caller domains, not a successful234 premise. -/
theorem source (f : Frontier) (s : High) (hs : FIw_ArrayValue.canonical s)
 (hf : ∀ d∈f.val,∀ x∈d.val,x.val<2147483647) (i : Fin 20) :
 Canon (high s i) ∧ (level i).val<20 ∧
 (∀ x∈(frontier f i).val,x.val<2147483647) ∧
 ∃ empty,FIq_Native.pool_v1.pair_forest_semantic_terminal.empty_root (level i)=ok empty ∧
 ∀ x∈empty.val,x.val<2147483647 := by
 refine ⟨NJB_ArrayCarrier.canonical_cell s hs _,by rw [level_value];exact i.isLt,?_,?_⟩
 · exact hf _ (List.getElem_mem _)
 · apply WP.spec_imp_exists
   apply JGa_EmptyRoot.source
   rw [level_value]
   have h:=i.isLt
   omega
#print source
#print axioms level_value
#print axioms source
end AspisR1.NJX_AppendDomains
end
