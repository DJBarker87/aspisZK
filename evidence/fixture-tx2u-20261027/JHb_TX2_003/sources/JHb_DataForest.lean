import Aeneas
set_option autoImplicit false
namespace AspisR1.JHb_DataForest
open Aeneas Aeneas.Std
def c00 : List U8 := [65#u8,83#u8,67#u8,56#u8,2#u8,8#u8,1#u8,254#u8,34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8,242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8,55#u8,157#u8,211#u8,124#u8,152#u8,170#u8,59#u8,88#u8]
theorem c00_length : c00.length=32 := by simp only [c00,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c00_length
def c01 : List U8 := [182#u8,77#u8,252#u8,152#u8,45#u8,26#u8,82#u8,63#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8]
theorem c01_length : c01.length=32 := by simp only [c01,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c01_length
def c02 : List U8 := [242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8,42#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,85#u8,246#u8,62#u8,4#u8,159#u8,80#u8,117#u8,33#u8,221#u8,239#u8,128#u8,120#u8,216#u8,131#u8,141#u8,49#u8]
theorem c02_length : c02.length=32 := by simp only [c02,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c02_length
def c03 : List U8 := [99#u8,239#u8,102#u8,35#u8,253#u8,148#u8,147#u8,6#u8,128#u8,120#u8,67#u8,103#u8,86#u8,177#u8,157#u8,56#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem c03_length : c03.length=32 := by simp only [c03,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c03_length
def c04 : List U8 := List.replicate 32 0#u8
theorem c04_length : c04.length=32 := by simp only [c04,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c04_length
def c05 : List U8 := List.replicate 32 0#u8
theorem c05_length : c05.length=32 := by simp only [c05,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c05_length
def bytes : List U8 := c00 ++ c01 ++ c02 ++ c03 ++ c04 ++ c05
theorem length : bytes.length=192 := by
  simp only [bytes,List.length_append,c00_length,c01_length,c02_length,c03_length,c04_length,c05_length]
#print axioms length
def value : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩
end AspisR1.JHb_DataForest
