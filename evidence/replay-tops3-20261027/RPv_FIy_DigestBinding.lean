import RPv_FIy_DigestClosed
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_DigestBinding
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon)
open FIw_ArrayValue (canonical decoded)

theorem value (output out : Array NQ 8#usize) (selector : NQ)
    (opened : Array NQ 16#usize) (start : Usize) (expected : Array U32 8#usize) (right : Bool)
    (hb : start.val+8≤16) (ho : canonical output) (hs : Canon selector) (ha : canonical opened)
    (he : ∀ x∈expected.val,x.val<FIw_ScalarArithmetic.P)
    (success : pool_v1.pair_forest_semantic_terminal.add_digest_binding output selector opened start expected right=ok out) :
    canonical out ∧ ∀ j : Fin (8#usize).val,
      decoded out j=decoded output j+FIy_DigestLane.increment selector opened start.val expected right j.val := by
  have source := FIy_DigestLoop.value 8 ⟨0#usize,poseidon2.DIGEST_ELEMS⟩ output out selector opened start expected right
    (by rw [poseidon2.DIGEST_ELEMS];rfl) (by rfl) hb ho hs ha he success
  refine ⟨source.1,?_⟩
  intro j
  rw [source.2,FIy_DigestClosed.value]
  have hj : j.val<8 := j.isLt
  simp only [show (0#usize).val=0 from rfl,Nat.zero_add,Nat.zero_le,hj,and_self,↓reduceIte]
#print axioms value
end AspisR1.FIy_DigestBinding
end
