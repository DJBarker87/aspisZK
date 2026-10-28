import RPz8_JFx_NativeBytes
import ExtractedTerminalDecoderSuccess
set_option autoImplicit false
namespace AspisR1.JFu_PublicHeader
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder.pool_v1.pair_forest_terminal

theorem length : JFx_NativeBytes.publicInput.length=1880 := JFx_NativeBytes.publicBytes_length

theorem first_eight : JFx_NativeBytes.publicInput.val.take 8 =
    [65#u8,83#u8,70#u8,56#u8,1#u8,1#u8,1#u8,3#u8] := by
  rfl

theorem header :
    JFx_NativeBytes.publicInput.val.take 4=POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC.val ∧
    JFx_NativeBytes.publicInput.val[4]?=some POOL_V1_PAIR_FOREST_TERMINAL_VERSION ∧
    JFx_NativeBytes.publicInput.val[5]?=some 1#u8 ∧
    JFx_NativeBytes.publicInput.val[6]?=some 1#u8 := by
  have p:=first_eight
  refine ⟨?_,?_,?_,?_⟩
  · have h:=congrArg (List.take 4) p
    simpa only [List.take_take,show min 4 8=4 from rfl, List.take_succ_cons,List.take_zero, POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC,Array.make] using h
  · have h:=congrArg (fun xs : List U8 => xs[4]?) p
    simpa only [List.getElem?_take_of_lt (by decide : 4<8),List.getElem?_cons_succ,List.getElem?_cons_zero, POOL_V1_PAIR_FOREST_TERMINAL_VERSION] using h
  · have h:=congrArg (fun xs : List U8 => xs[5]?) p
    simpa only [List.getElem?_take_of_lt (by decide : 5<8),List.getElem?_cons_succ,List.getElem?_cons_zero] using h
  · have h:=congrArg (fun xs : List U8 => xs[6]?) p
    simpa only [List.getElem?_take_of_lt (by decide : 6<8),List.getElem?_cons_succ,List.getElem?_cons_zero] using h

#print axioms length
#print axioms first_eight
#print axioms header
end AspisR1.JFu_PublicHeader
