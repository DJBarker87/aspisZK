import NHF_ViewResult
set_option autoImplicit false
namespace AspisR1.NHF_SegmentedFrame
open Aeneas Aeneas.Std
/-- Every original proof has this representation, with no value restriction. -/
theorem represent (bytes : List U8) (size : bytes.length=57607) :
 (bytes.take 7495).length=7495 ∧
 ((bytes.drop 7495).take 32).length=32 ∧
 (bytes.drop 7527).length=50080 ∧
 bytes.take 7495 ++ (bytes.drop 7495).take 32 ++ bytes.drop 7527=bytes := by
 have a : (bytes.take 7495).length=7495 := by simp only [List.length_take,size];omega
 have b : ((bytes.drop 7495).take 32).length=32 := by
   simp only [List.length_take,List.length_drop,size];omega
 have c : (bytes.drop 7527).length=50080 := by simp only [List.length_drop,size]
 refine ⟨a,b,c,?_⟩
 have split : bytes.drop 7495=(bytes.drop 7495).take 32 ++ (bytes.drop 7495).drop 32 :=
   (List.take_append_drop 32 (bytes.drop 7495)).symm
 have tail : (bytes.drop 7495).drop 32=bytes.drop 7527 := by rw [List.drop_drop]
 calc
  bytes.take 7495 ++ (bytes.drop 7495).take 32 ++ bytes.drop 7527 =
    bytes.take 7495 ++ ((bytes.drop 7495).take 32 ++ (bytes.drop 7495).drop 32) := by
      rw [tail,List.append_assoc]
  _=bytes.take 7495 ++ bytes.drop 7495 := by rw [←split]
  _=bytes := List.take_append_drop 7495 bytes
/-- The native checked offset7495/length32 is exactly the same middle field. -/
theorem middle (header inactive suffix : List U8)
 (headSize : header.length=7495) (middleSize : inactive.length=32) :
 ((header++inactive++suffix).drop 7495).take 32=inactive := by
 rw [List.append_assoc,←headSize,List.drop_left,←middleSize,List.take_left]
/-- No invented trailing bytes are needed to realize the complete native input. -/
theorem length (header inactive suffix : List U8)
 (headSize : header.length=7495) (middleSize : inactive.length=32)
 (tailSize : suffix.length=50080) :
 (header++inactive++suffix).length=57607 := by
 simp only [List.length_append,headSize,middleSize,tailSize]
#print axioms represent
#print axioms middle
#print axioms length
end AspisR1.NHF_SegmentedFrame
