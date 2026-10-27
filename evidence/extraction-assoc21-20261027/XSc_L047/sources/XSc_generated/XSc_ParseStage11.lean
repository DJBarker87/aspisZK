import XSc_ParseStage12
import XSc_ParseResume
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_ParseStage11
theorem source (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 : Slice U8) (offset : Usize) :
 XSc_ParseCuts.tail11 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 offset =
 XSc_ParseResume.run bytes root 11 16 ([r0,r11,r21,r31,r41,r51,r61,r71,r81,r91,r101],offset) := by
 unfold XSc_ParseCuts.tail11
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
   XSc_ParseStage12.source bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 record next
#print axioms source
end XSc_ParseStage11
