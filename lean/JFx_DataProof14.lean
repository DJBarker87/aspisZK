import Aeneas
set_option autoImplicit false
namespace AspisR1.JFx_DataProof14
open Aeneas Aeneas.Std
def c00 : List U8 := List.replicate 32 0#u8
theorem c00_length : c00.length = 32 := by simp only [c00,List.length_replicate]
#print axioms c00_length
def c01 : List U8 := List.replicate 32 0#u8
theorem c01_length : c01.length = 32 := by simp only [c01,List.length_replicate]
#print axioms c01_length
def c02 : List U8 := List.replicate 32 0#u8
theorem c02_length : c02.length = 32 := by simp only [c02,List.length_replicate]
#print axioms c02_length
def c03 : List U8 := List.replicate 32 0#u8
theorem c03_length : c03.length = 32 := by simp only [c03,List.length_replicate]
#print axioms c03_length
def c04 : List U8 := List.replicate 32 0#u8
theorem c04_length : c04.length = 32 := by simp only [c04,List.length_replicate]
#print axioms c04_length
def c05 : List U8 := List.replicate 32 0#u8
theorem c05_length : c05.length = 32 := by simp only [c05,List.length_replicate]
#print axioms c05_length
def c06 : List U8 := List.replicate 32 0#u8
theorem c06_length : c06.length = 32 := by simp only [c06,List.length_replicate]
#print axioms c06_length
def c07 : List U8 := List.replicate 32 0#u8
theorem c07_length : c07.length = 32 := by simp only [c07,List.length_replicate]
#print axioms c07_length
def c08 : List U8 := List.replicate 7 0#u8
theorem c08_length : c08.length = 7 := by simp only [c08,List.length_replicate]
#print axioms c08_length
def bytes : List U8 := (((c00 ++ c01) ++ (c02 ++ c03)) ++ ((c04 ++ c05) ++ (c06 ++ (c07 ++ c08))))
theorem length : bytes.length = 263 := by
  simp only [bytes,List.length_append,c00_length,c01_length,c02_length,c03_length,c04_length,c05_length,c06_length,c07_length,c08_length]
#print axioms length
end AspisR1.JFx_DataProof14
