import NFW_StoredWindows
set_option autoImplicit false
namespace AspisR1.NFW_FoldedPayload
open Aeneas Aeneas.Std Result
/-- Source alpha1 payload has exactly the original root followed by round1. -/
theorem length (root tail : List U8) (hr : root.length=32) (ht : tail.length=224) :
 (root++tail).length=256 := by simp [hr,ht]
theorem selected (root tail : List U8) (hr : root.length=32) (i : Nat) :
 (root++tail)[i]?=if i<32 then root[i]? else tail[i-32]? := by
 simp only [List.getElem?_append,hr]
theorem rejoin (proof : List U8) :
 (proof.drop 7751).take 32 ++ ((proof.drop 7751).drop 32).take 224 =
 (proof.drop 7751).take 256 := by
 have law := List.take_add 32 224 (proof.drop 7751)
 exact law.symm
#print axioms length
#print axioms selected
#print axioms rejoin
end AspisR1.NFW_FoldedPayload
