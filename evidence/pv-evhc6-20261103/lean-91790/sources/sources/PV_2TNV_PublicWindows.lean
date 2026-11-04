import PV_2TNV_PublicEncoding
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_PublicWindows
open Aeneas Aeneas.Std PV_2TNV_PublicEncoding

theorem nested {A : Type} (bytes : List A) (off n start count : Nat)
    (bound : start+count ≤ n) :
    (((bytes.drop off).take n).drop start).take count =
      (bytes.drop (off+start)).take count := by
  simp only [List.drop_take,List.drop_drop,List.take_take]
  rw [Nat.min_eq_left (by omega : count ≤ n-start)]

theorem digest_window (bytes literal : List U8) (off : Nat)
    (selected : (bytes.drop off).take 32 = literal) :
    digest bytes off = digest literal 0 := by
  funext i
  unfold digest word
  have h := nested bytes off 32 (4*i.val) 4 (by have := i.isLt; omega)
  rw [←h, selected, Nat.zero_add]
#print axioms nested
#print axioms digest_window
end AspisR1.PV_2TNV_PublicWindows
