import XSc_ParseStage04
import XSc_ParseResume
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_ParseStage03
theorem source (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 : Slice U8) (offset : Usize) :
 XSc_ParseCuts.tail3 bytes root r0 r11 r21 offset =
 XSc_ParseResume.run bytes root 3 24 ([r0,r11,r21],offset) := by
 unfold XSc_ParseCuts.tail3
 rw [XSc_ParseResume.advance]
 simp only [XRz_ParseFold.row,Nat.reduceLT,_root_.dite_true,U8.ofNat,Nat.reduceAdd]
 congr 1
 funext parsed
 cases parsed with
 | Err e => rfl
 | Ok pair =>
  rcases pair with ⟨record,next⟩
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  dsimp! only
  simpa only [List.append_nil,List.cons_append,List.nil_append] using
   XSc_ParseStage04.source bytes root r0 r11 r21 record next
#print axioms source
end XSc_ParseStage03
