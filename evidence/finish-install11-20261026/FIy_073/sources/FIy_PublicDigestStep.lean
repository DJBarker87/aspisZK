import FIy_Frontier20
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_PublicDigestStep
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIy_FrontierStep (Selectors)

def model (s : Selectors) (a : Array NQ 16#usize) (row : Nat) (expected : Array U32 8#usize)
    (old : Fin (8#usize).val → K) : Fin (8#usize).val → K := fun j=>
  old j+FIy_FrontierMeaning.rowValue s row*(FIv_NativeArray.value a j.val-
    (FIy_DigestLane.target expected false j.val : K))

theorem value (d out : Array NQ 8#usize) (s : Selectors) (a : Array NQ 16#usize)
    (row : Usize) (selector : NQ) (expected : Array U32 8#usize)
    (hd : canonical d) (hh : canonical s.high) (hl : canonical s.low) (ha : canonical a)
    (he : ∀ x∈expected.val,x.val<FIw_ScalarArithmetic.P)
    (hselector : pool_v1.pair_forest_copy_terminal.Selectors.row s row=ok selector)
    (success : pool_v1.pair_forest_semantic_terminal.add_digest_binding d selector a 0#usize expected false=ok out) :
    canonical out ∧ decoded out=model s a row.val expected (decoded d) := by
  have sv := FIw_SelectorRow.value_exact s row selector hh hl hselector
  have dv := FIy_DigestBinding.value d out selector a 0#usize expected false (by decide) hd sv.1 ha he success
  refine ⟨dv.1,funext (fun j=>?_ )⟩
  rw [dv.2 j]
  simp only [model,FIy_DigestLane.increment,sv.2,FIy_FrontierMeaning.rowValue,
    show (0#usize).val=0 from rfl,Nat.zero_add]

theorem row (block offset base out : Usize)
    (hm : block*16#usize=ok base) (ha : base+offset=ok out) : out.val=block.val*16+offset.val := by
  have mv := FIw_WordValue.mul block 16#usize base hm
  have av := FIw_WordValue.add base offset out ha
  rw [mv] at av
  exact av
#print axioms value
#print axioms row
end AspisR1.FIy_PublicDigestStep
end
