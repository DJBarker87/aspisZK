import NJP_WriteCarrier

set_option autoImplicit false
namespace NJP_CheckedWords
open Aeneas Aeneas.Std Result

/-- Checked scalar facts used by the physical cohort node; all bounds follow
from the native row invariant and are not new caller hypotheses. -/
theorem add_one (i : Usize) (bound : i.val<16) :
 ∃ next, i+1#usize=ok next  ∧  next.val=i.val+1 := by
 have spec : (i+1#usize) ⦃ next => next.val=i.val+1 ⦄ := by
   step* <;> scalar_tac
 exact WP.spec_imp_exists spec

theorem add_two (i : Usize) (bound : i.val+2 ≤ 16) :
 ∃ next, i+2#usize=ok next  ∧  next.val=i.val+2 := by
 have spec : (i+2#usize) ⦃ next => next.val=i.val+2 ⦄ := by
   step* <;> scalar_tac
 exact WP.spec_imp_exists spec

theorem add_window (at1 : Usize) (bound : at1.val ≤ 9216) :
 ∃ next, at1+32#usize=ok next  ∧  next.val=at1.val+32 := by
 have spec : (at1+32#usize) ⦃ next => next.val=at1.val+32 ⦄ := by
   step* <;> scalar_tac
 exact WP.spec_imp_exists spec

theorem subtract (length at1 : Usize) (bound : at1.val ≤ length.val) :
 ∃ remaining, length-at1=ok remaining  ∧  remaining.val=length.val-at1.val := by
 have spec : (length-at1) ⦃ remaining => remaining.val=length.val-at1.val ⦄ := by
   step* <;> scalar_tac
 exact WP.spec_imp_exists spec

theorem half (index : U32) :
 ∃ parent, index/2#u32=ok parent  ∧  parent.val=index.val/2 := by
 have spec : (index/2#u32) ⦃ parent => parent.val=index.val/2 ⦄ := by
   step* <;> scalar_tac
 exact WP.spec_imp_exists spec

#print add_one
#print axioms add_one
#print add_two
#print axioms add_two
#print add_window
#print axioms add_window
#print subtract
#print axioms subtract
#print half
#print axioms half
end NJP_CheckedWords
