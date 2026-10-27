import XSc_ParseStage08
import XSc_ParseResume
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_ParseStage07
theorem source (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 : Slice U8) (offset : Usize) :
 XSc_ParseCuts.tail7 bytes root r0 r11 r21 r31 r41 r51 r61 offset =
 XSc_ParseResume.run bytes root 7 20 ([r0,r11,r21,r31,r41,r51,r61],offset) := by
 unfold XSc_ParseCuts.tail7
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
   XSc_ParseStage08.source bytes root r0 r11 r21 r31 r41 r51 r61 record next
#print axioms source
end XSc_ParseStage07
