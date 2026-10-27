import XSg_OldStage13
import XSg_OldResume
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSg_OldStage12
theorem source (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 : Slice U8) (offset : Usize) :
 XSg_OldCuts.tail12 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 offset =
 XSg_OldResume.run bytes root 12 15 ([r0,r11,r21,r31,r41,r51,r61,r71,r81,r91,r101,r111],offset) := by
 unfold XSg_OldCuts.tail12
 rw [XSg_OldResume.advance]
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
   XSg_OldStage13.source bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 record next
#print axioms source
end XSg_OldStage12
