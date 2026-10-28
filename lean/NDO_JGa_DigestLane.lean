import NDO_JGa_DigestTarget
import RPv_FIy_DigestLane
import RPv_JFy_Steps
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_DigestLane
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)

@[step] theorem arithmetic (old selector cell : field.QM31) (target : U32)
    (ho : Canon old) (hs : Canon selector) (hc : Canon cell) (ht : target.val<FIw_ScalarArithmetic.P) :
    FIy_DigestArithmetic.run old selector cell target ⦃ out => Canon out ⦄ := by
  unfold FIy_DigestArithmetic.run
  step*
#print axioms arithmetic

@[step] theorem source (lane : Usize) (output : Array field.QM31 8#usize) (selector : field.QM31)
    (opened : Array field.QM31 16#usize) (start : Usize) (expected : Array U32 8#usize) (right : Bool)
    (hl : lane.val<8) (hb : start.val+8≤16) (ho : canonical output) (hs : Canon selector)
    (ha : canonical opened) (he : ∀ x∈expected.val,x.val<FIw_ScalarArithmetic.P) :
    FIy_DigestLane.run lane output selector opened start expected right ⦃ out => canonical out ⦄ := by
  have read : Array.index_usize expected lane ⦃ _ => True ⦄ := by step* <;> scalar_tac
  obtain ⟨t,ht,_⟩ := WP.spec_imp_exists read
  have hc := he t (List.mem_of_getElem? (FIy_ArraySlot.value expected lane t ht))
  unfold FIy_DigestLane.run
  rw [ht,bind_tc_ok]
  step* <;> first | assumption | scalar_tac
#print axioms source
end AspisR1.JGa_DigestLane
end
