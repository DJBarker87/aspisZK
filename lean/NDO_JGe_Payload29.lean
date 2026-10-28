import NDO_JGe_Window29_00
import NDO_JGe_WindowAssembly
import JGe_ValuesAssembly
import NDO_JFw_Y1
set_option autoImplicit false
namespace AspisR1.JGe_Payload29
open Aeneas Aeneas.Std Result
open JGe_Window29
attribute [local irreducible] JFx_NativeBytes.proofBytes
def rawChunks : List (List U8) := [c00,c01,c02,c03,c04,c05,c06]
theorem retained : (JFw_Frames.window 7527 224).val=rawChunks.flatten := by
  have h := JGe_WindowAssembly.source 32 7 7527
  simpa only [JGe_WindowAssembly.chunks,Nat.reduceAdd,rawChunks,selected00,selected01,selected02,selected03,selected04,selected05,selected06] using h
#print axioms retained
def value : Slice U8 := JFw_Frames.window 7527 224
theorem length : value.length=224 := JFw_Frames.window_length 7527 224 (by decide)
#print axioms length
end AspisR1.JGe_Payload29
