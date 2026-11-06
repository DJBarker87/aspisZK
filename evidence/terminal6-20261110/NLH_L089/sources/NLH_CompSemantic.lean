import NKI_InitialPrefix
import NLH_CompositionState
import NLH_SemanticFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_CompSemantic
open Aeneas Aeneas.Std Result FIq_Native NLH_CompositionState
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public)
/--261 is consumed at the exact openings and selectors already in this parent
state. All domains are explicit input invariants, discharged by the root's gathers. -/
theorem source (pub : Public) (claims : Array FIv_NativeArithmetic.NQ 84#usize)
 (point : Array FIv_NativeArithmetic.NQ 10#usize) (lambda chi theta : FIv_NativeArithmetic.NQ) (st : State)
 (hd : NKR_DigestChildren.Domain pub) (hz : canonical st.openings.z) (hs : canonical st.openings.succ_z)
 (hx : canonical st.openings.xor12_z) (hh : canonical st.selectors.high) (hl : canonical st.selectors.low)
 (asset : pub.asset_id.val < 2147483647)
 (amount : (core.option.Option.unwrap_or pub.withdrawal_amount 0#u32).val < 2147483647) :
 ∃ value,step pub claims point lambda chi theta .semantic st=ok (.Ok {st with semantic := value}) ∧
 canonical value ∧ pool_v1.pair_forest_semantic_terminal.semantic_packed pub st.openings st.selectors=ok value := by
 obtain ⟨final,_,_,canon,call,_⟩ := NLH_SemanticFold.source pub st.openings st.selectors hd hz hs hx hh hl asset amount
 exact ⟨final.packed,by simp only [step,call,bind_tc_ok],canon,call⟩
#print axioms source
end AspisR1.NLH_CompSemantic
end
