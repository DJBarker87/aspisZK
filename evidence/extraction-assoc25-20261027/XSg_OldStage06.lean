import XSg_OldStage07
import XSg_OldResume
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSg_OldStage06
theorem source (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 : Slice U8) (offset : Usize) :
 XSg_OldCuts.tail6 bytes root r0 r11 r21 r31 r41 r51 offset =
 XSg_OldResume.run bytes root 6 21 ([r0,r11,r21,r31,r41,r51],offset) := by
 unfold XSg_OldCuts.tail6
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
   XSg_OldStage07.source bytes root r0 r11 r21 r31 r41 r51 record next
#print axioms source
end XSg_OldStage06
