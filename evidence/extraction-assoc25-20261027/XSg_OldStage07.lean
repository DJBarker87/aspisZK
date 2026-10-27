import XSg_OldStage08
import XSg_OldResume
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSg_OldStage07
theorem source (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 : Slice U8) (offset : Usize) :
 XSg_OldCuts.tail7 bytes root r0 r11 r21 r31 r41 r51 r61 offset =
 XSg_OldResume.run bytes root 7 20 ([r0,r11,r21,r31,r41,r51,r61],offset) := by
 unfold XSg_OldCuts.tail7
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
   XSg_OldStage08.source bytes root r0 r11 r21 r31 r41 r51 r61 record next
#print axioms source
end XSg_OldStage07
