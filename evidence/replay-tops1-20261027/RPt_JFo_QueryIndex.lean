import RPt_JFo_Prepared
import RPt_JFo_Index
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_QueryIndex
open Aeneas Aeneas.Std Result WP

theorem source (a : Array U32 22#usize) (i : Usize) (bound : i.val<22)
    (word : U32) (selected : a.val[i.val]?=some word) : Array.index_usize a i=ok word := by
  have spec : Array.index_usize a i ⦃ out => out=word ⦄ := by
    step*
    simp_all
  obtain ⟨out,call,same⟩ := WP.spec_imp_exists spec
  exact same ▸ call

#print axioms source
end AspisR1.JFo_QueryIndex
end
