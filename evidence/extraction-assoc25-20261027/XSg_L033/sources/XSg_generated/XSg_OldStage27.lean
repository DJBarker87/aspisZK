import XSg_OldCuts
import XSg_OldResume
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSg_OldStage27
theorem source (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 r211 r221 r231 r241 r251 r261 : Slice U8) (offset : Usize) :
 XSg_OldCuts.tail27 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 r211 r221 r231 r241 r251 r261 offset =
 XSg_OldResume.run bytes root 27 0 ([r0,r11,r21,r31,r41,r51,r61,r71,r81,r91,r101,r111,r121,r131,r141,r151,r161,r171,r181,r191,r201,r211,r221,r231,r241,r251,r261],offset) := by
 unfold XSg_OldCuts.tail27 XSg_OldResume.run XRx_TryDriver.run XSe_ParseFinish.finish
 rfl
#print axioms source
end XSg_OldStage27
