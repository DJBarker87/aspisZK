import NDO_JGe_Window31_00
import NDO_JGe_Window31_08
import NDO_JGe_Window31_16
import NDO_JGe_Window31_24
import NDO_JGe_Window31_32
import NDO_JGe_Window31_40
import NDO_JGe_Window31_48
import NDO_JGe_Window31_56
import NDO_JGe_WindowAssembly
import JGe_ValuesAssembly
import NDO_JFw_Y1
set_option autoImplicit false
namespace AspisR1.JGe_Payload31
open Aeneas Aeneas.Std Result
open JGe_Window31
attribute [local irreducible] JFx_NativeBytes.proofBytes
def rawChunks : List (List U8) := [c00,c01,c02,c03,c04,c05,c06,c07,c08,c09,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,c48,c49,c50,c51,c52,c53,c54,c55,c56,c57,c58,c59,c60,c61,c62,c63]
theorem retained : (JFw_Frames.window 8007 2048).val=rawChunks.flatten := by
  have h := JGe_WindowAssembly.source 32 64 8007
  simpa only [JGe_WindowAssembly.chunks,Nat.reduceAdd,rawChunks,selected00,selected01,selected02,selected03,selected04,selected05,selected06,selected07,selected08,selected09,selected10,selected11,selected12,selected13,selected14,selected15,selected16,selected17,selected18,selected19,selected20,selected21,selected22,selected23,selected24,selected25,selected26,selected27,selected28,selected29,selected30,selected31,selected32,selected33,selected34,selected35,selected36,selected37,selected38,selected39,selected40,selected41,selected42,selected43,selected44,selected45,selected46,selected47,selected48,selected49,selected50,selected51,selected52,selected53,selected54,selected55,selected56,selected57,selected58,selected59,selected60,selected61,selected62,selected63] using h
#print axioms retained
def value : Slice U8 := JFw_Frames.window 8007 2048
theorem length : value.length=2048 := JFw_Frames.window_length 8007 2048 (by decide)
#print axioms length
end AspisR1.JGe_Payload31
