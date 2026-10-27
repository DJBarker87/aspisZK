import RPt_BEm_PaddingCut
set_option autoImplicit false
namespace AspisR1.BEm_PaddingGeometry
open BEm_PaddingModel

/-- Fixed eight-byte word cuts commute with byte-prefix removal. No concrete
padding suffix is expanded; this is the list model's symbolic layout law. -/
theorem drop_words (words : List Word) (n : Nat) :
    (words.flatMap bytes).drop (8*n) = (words.drop n).flatMap bytes := by
  induction n generalizing words with
  | zero => simp
  | succ n ih =>
    cases words with
    | nil => simp
    | cons w rest =>
      simp only [List.flatMap_cons,List.drop_succ_cons]
      have head : (bytes w).length=8 := rfl
      calc
        (bytes w ++ rest.flatMap bytes).drop (8*(n+1)) =
            ((bytes w ++ rest.flatMap bytes).drop 8).drop (8*n) := by
          simp only [List.drop_drop]
          congr 1
          omega
        _ = (rest.flatMap bytes).drop (8*n) := by rw [←head,List.drop_left]
        _ = (rest.drop n).flatMap bytes := ih rest

/-- The32-byte node-count cut is exactly four8-byte padding words in the
list model, including count0 and an empty suffix. Physical Rust association
is still a separate gate. -/
theorem counted (words : List Word) (validWords : ∀ w ∈ words, valid w) (count : Nat) :
    ((words.flatMap bytes).drop (32*count)).any (fun b => decide (b≠0)) =
      (words.drop (4*count)).any nativeWord := by
  rw [show 32*count=8*(4*count) by omega,drop_words]
  exact (BEm_PaddingCut.cut words validWords count).symm

#print axioms drop_words
#print axioms counted
end AspisR1.BEm_PaddingGeometry
