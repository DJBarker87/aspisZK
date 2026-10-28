import NDO_JFt_Index
import NDO_JFs_PrefixRead
import NDO_JFu_PublicHeader
set_option autoImplicit false
namespace AspisR1.JFs_PublicHeader
open Aeneas Aeneas.Std Result WP
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal

def magic : Slice U8 := ⟨[65#u8,83#u8,70#u8,56#u8],by simp;scalar_tac⟩

theorem firstn : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
    JFx_NativeBytes.publicInput {«end»:=4#usize}=ok magic := by
  have header : JFx_NativeBytes.publicInput.val.take 4=magic.val := by
    simpa only [POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC,Array.make,magic] using JFu_PublicHeader.header.1
  apply JFs_PrefixRead.source _ _ (by rw [JFu_PublicHeader.length];decide)
  simpa only [show (4#usize).val=4 from rfl] using header

theorem index (i : Usize) (inside : i.val<8) (byte : U8)
    (value : ([65#u8,83#u8,70#u8,56#u8,1#u8,1#u8,1#u8,3#u8] : List U8)[i.val]?=some byte) :
    Slice.index_usize JFx_NativeBytes.publicInput i=ok byte := by
  apply JFt_Index.source _ _ (by rw [JFu_PublicHeader.length];omega) byte
  have h:=congrArg (fun xs : List U8 => xs[i.val]?) JFu_PublicHeader.first_eight
  rw [List.getElem?_take_of_lt inside] at h
  exact h.trans value

#print axioms firstn
#print axioms index
end AspisR1.JFs_PublicHeader
