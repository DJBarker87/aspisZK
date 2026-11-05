import NGW_DotCodec
import Port3_PushFrame
set_option autoImplicit false
namespace NGW_DotStep
open Aeneas Aeneas.Std Result AspisR1
abbrev Dot := NGM_DotABI.Dot

def interpret : core.result.Result (NGW_DotRef.Dot × Usize) U8 →
 core.result.Result (Dot × Usize) AspisR1Stage2.verifier.Error
 | .Ok (d,i) => .Ok (NGW_DotCodec.fromRef d,i)
 | .Err _ => .Err .Parse

theorem pack_total (d : Dot) : ∃ w,NGW_DotRef.pack (NGW_DotCodec.toRef d)=ok w := by
 rcases d with ⟨⟨left⟩,⟨right⟩,count⟩
 obtain ⟨a,b,c,d,hl⟩ := NGM_ArrayFour.shape left
 obtain ⟨e,f,g,h,hr⟩ := NGM_ArrayFour.shape right
 subst left
 subst right
 simp [NGW_DotRef.pack,NGW_DotCodec.toRef,Array.make,Array.index_usize,lift]

theorem source (updated : Dot) (index : Usize) (accepted : Bool)
 (domain : accepted=true → updated.count.val ≤ 64) :
 (do let w ← NGW_DotRef.pack (NGW_DotCodec.toRef updated)
     let r ← NGW_DotRef.push_result w index accepted
     ok (interpret r)) =
 ok (NGM_DotABI.stepResult updated index (if accepted then .Ok () else .Err ())) := by
 cases accepted with
 | false =>
   obtain ⟨w,hw⟩ := pack_total updated
   simp only [hw,NGW_DotRef.push_result,bind_tc_ok,interpret,NGM_DotABI.stepResult,Bool.false_eq_true,if_false]
 | true =>
   have codec := NGW_DotCodec.unpack_pack updated (domain rfl)
   obtain ⟨w,hw,rest⟩ := Port3_PushFrame.bind_success _ _ _ codec
   obtain ⟨d,hd,rest⟩ := Port3_PushFrame.bind_success _ _ _ rest
   have same := Result.ok.inj rest
   simp only [hw,NGW_DotRef.push_result,hd,bind_tc_ok,lift,interpret,NGM_DotABI.stepResult,if_true,same]

#print axioms pack_total
#print axioms source
end NGW_DotStep
