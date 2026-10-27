import XSc_ParseStage15
import XSc_ParseResume
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_ParseStage14
theorem source (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 : Slice U8) (offset : Usize) :
 XSc_ParseCuts.tail14 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 offset =
 XSc_ParseResume.run bytes root 14 13 ([r0,r11,r21,r31,r41,r51,r61,r71,r81,r91,r101,r111,r121,r131],offset) := by
 unfold XSc_ParseCuts.tail14
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
   XSc_ParseStage15.source bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 record next
#print axioms source
end XSc_ParseStage14
