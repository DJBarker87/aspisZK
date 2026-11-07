import NNG_Erase_r
import NNG_FinishTree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TreeEmission
open Aeneas Aeneas.Std Result NNG_Emitted NMT_CallTree
/-- Lexical fission changes only the names of continuations. -/
theorem tree_suffixes {H W : Type} (c : Calls) (s : Parent H W) :
    NNG_FinishTree.tree c s = NNG_TreeSuffixes.f_r c s := by rfl
#print axioms tree_suffixes

/-- The original unannotated suffixes are the exact fresh emitted body. -/
theorem source_suffixes {H W : Type} (c : Calls) (s : Parent H W) :
    NNG_SourceSuffixes.f_r c s = NNG_Emitted.emitted c s := by rfl
#print axioms source_suffixes

/-- Composes the checked small suffix erasures, with no whole-body reduction
of any child. Every Result and stopped continuation is retained. -/
theorem erase_tree {H W : Type} (c : Calls) (s : Parent H W) :
    erase (NNG_FinishTree.tree c s) = NNG_Emitted.emitted c s := by
  rw [tree_suffixes, NNG_TreeErasure.erase_r, source_suffixes]
#print axioms erase_tree
end AspisR1.NNG_TreeEmission
