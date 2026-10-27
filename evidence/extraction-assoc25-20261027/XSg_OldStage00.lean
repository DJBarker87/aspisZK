import XSg_OldStage01
import XSg_OldResume
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSg_OldStage00
theorem source (bytes : Slice U8) (root : Array U8 32#usize) (offset : Usize) :
 XSg_OldCuts.tail0 bytes root offset =
 XSg_OldResume.run bytes root 0 27 ([],offset) := by
 unfold XSg_OldCuts.tail0
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
   XSg_OldStage01.source bytes root record next
#print axioms source
end XSg_OldStage00
