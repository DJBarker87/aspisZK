import XSg_OldStage03
import XSg_OldResume
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSg_OldStage02
theorem source (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 : Slice U8) (offset : Usize) :
 XSg_OldCuts.tail2 bytes root r0 r11 offset =
 XSg_OldResume.run bytes root 2 25 ([r0,r11],offset) := by
 unfold XSg_OldCuts.tail2
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
   XSg_OldStage03.source bytes root r0 r11 record next
#print axioms source
end XSg_OldStage02
