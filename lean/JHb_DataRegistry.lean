import Aeneas
set_option autoImplicit false
namespace AspisR1.JHb_DataRegistry
open Aeneas Aeneas.Std
def c00 : List U8 := [65#u8,83#u8,82#u8,50#u8,3#u8,2#u8,1#u8,255#u8,34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8,242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8,55#u8,157#u8,211#u8,124#u8,152#u8,170#u8,59#u8,88#u8]
theorem c00_length : c00.length=32 := by simp only [c00,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c00_length
def c01 : List U8 := [182#u8,77#u8,252#u8,152#u8,45#u8,26#u8,82#u8,63#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem c01_length : c01.length=32 := by simp only [c01,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c01_length
def c02 : List U8 := [0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8]
theorem c02_length : c02.length=32 := by simp only [c02,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c02_length
def c03 : List U8 := [7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,1#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,1#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8]
theorem c03_length : c03.length=32 := by simp only [c03,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c03_length
def c04 : List U8 := [68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,2#u8,168#u8,246#u8,145#u8,78#u8,136#u8,161#u8,176#u8]
theorem c04_length : c04.length=32 := by simp only [c04,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c04_length
def c05 : List U8 := [226#u8,16#u8,21#u8,62#u8,247#u8,99#u8,174#u8,43#u8,0#u8,194#u8,185#u8,61#u8,22#u8,193#u8,36#u8,210#u8,192#u8,83#u8,122#u8,16#u8,4#u8,128#u8,0#u8,0#u8,10#u8,229#u8,72#u8,238#u8,230#u8,11#u8,166#u8,244#u8]
theorem c05_length : c05.length=32 := by simp only [c05,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c05_length
def c06 : List U8 := [18#u8,189#u8,102#u8,59#u8,14#u8,251#u8,113#u8,3#u8,126#u8,115#u8,18#u8,70#u8,185#u8,8#u8,39#u8,166#u8,11#u8,127#u8,135#u8,77#u8,165#u8,209#u8,161#u8,69#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8]
theorem c06_length : c06.length=32 := by simp only [c06,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c06_length
def c07 : List U8 := [165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,165#u8,255#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem c07_length : c07.length=32 := by simp only [c07,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c07_length
def bytes : List U8 := c00 ++ c01 ++ c02 ++ c03 ++ c04 ++ c05 ++ c06 ++ c07
theorem length : bytes.length=256 := by
  simp only [bytes,List.length_append,c00_length,c01_length,c02_length,c03_length,c04_length,c05_length,c06_length,c07_length]
#print axioms length
def value : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩
end AspisR1.JHb_DataRegistry
