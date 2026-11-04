import NFW_StoredLayout
set_option autoImplicit false
namespace AspisR1.NFW_StoredWindows
open Aeneas Aeneas.Std Result NFW_StoredLayout
def window (xs : List U8) (start width : Nat) : List U8 := (xs.drop start).take width
/-- The range domain follows from the SAME accepted proof length. -/
theorem width (xs : List U8) (length : xs.length=proofBytes) (start count : Nat)
 (inside : (start,count)∈windows) : (window xs start count).length=count := by
 have valid := bounds start count inside
 simp only [window,List.length_take,List.length_drop,length]
 omega
/-- Splitting and reassembling the same caller-owned scratch keeps both exact
child buffers; no independently chosen final vector is assumed. -/
theorem join (semantic y1 : List U8) (semWidth : semantic.length=13831)
 (yWidth : y1.length=928) :
 (semantic++y1).take 13831=semantic ∧ (semantic++y1).drop 13831=y1 ∧ (semantic++y1).length=14759 := by
 constructor
 · have h : (semantic++y1).take semantic.length=semantic := List.take_left
   simpa only [semWidth] using h
 constructor
 · have h : (semantic++y1).drop semantic.length=y1 := List.drop_left
   simpa only [semWidth] using h
 · simp only [List.length_append,semWidth,yWidth]
/-- Original proof input is immutable throughout all selected borrowed views. -/
theorem selected (xs : List U8) (start width offset : Nat) (inside : offset<width)
 (bound : start+width≤xs.length) :
 (window xs start width)[offset]?=xs[start+offset]? := by
 simp only [window,List.getElem?_take,inside,↓reduceIte,List.getElem?_drop]
#print axioms width
#print axioms join
#print axioms selected
end AspisR1.NFW_StoredWindows
