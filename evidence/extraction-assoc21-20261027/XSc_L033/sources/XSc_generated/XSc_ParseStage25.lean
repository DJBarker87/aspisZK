import XSc_ParseStage26
import XSc_ParseResume
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_ParseStage25
theorem source (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 r211 r221 r231 r241 : Slice U8) (offset : Usize) :
 XSc_ParseCuts.tail25 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 r211 r221 r231 r241 offset =
 XSc_ParseResume.run bytes root 25 2 ([r0,r11,r21,r31,r41,r51,r61,r71,r81,r91,r101,r111,r121,r131,r141,r151,r161,r171,r181,r191,r201,r211,r221,r231,r241],offset) := by
 unfold XSc_ParseCuts.tail25
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
   XSc_ParseStage26.source bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 r211 r221 r231 r241 record next
#print axioms source
end XSc_ParseStage25
