import NBZ_Carrier
set_option autoImplicit false
namespace NBZ_WordFrame
open Aeneas Aeneas.Std Result
abbrev Row := NBF_Frame.Row
abbrev Raw := NBF_Frame.Raw
def rowWrite (row : Row) (k : Fin 4) (word : U64) : Row :=
 ⟨row.val.set k.val word,by simp only [List.length_set];exact row.property⟩
/-- Exact selected-word effect plus unchanged exterior, on the actual nested
Vec/Array carrier. This is the composition rule for the eight-byte native cut. -/
theorem nested (raw : Raw) (index : Usize) (old : Row)
 (read : raw.val[index.val]?=some old) (k : Fin 4) (word : U64) (j l : Nat) :
 ((raw.set index (rowWrite old k word)).val[j]?).bind (fun row=>row.val[l]?)=
 if j=index.val ∧ l=k.val then some word else
   (raw.val[j]?).bind (fun row=>row.val[l]?) := by
 have active : index.val<raw.val.length := by
   by_contra h
   rw [List.getElem?_eq_none (by omega)] at read
   cases read
 by_cases sameRow : j=index.val
 · subst j
   change ((raw.val.set index.val (rowWrite old k word))[index.val]?).bind _=_
   rw [List.getElem?_set]
   simp only [active,if_pos,Option.bind_some,read,true_and]
   change (old.val.set k.val word)[l]?=_
   rw [List.getElem?_set]
   have inside : k.val<old.val.length := by rw [old.property];exact k.isLt
   by_cases sameWord : l=k.val
   · subst l
     simp only [inside,if_pos,true_and]
   · simp only [if_neg sameWord,if_neg (Ne.symm sameWord)]
 · rw [NBF_Frame.set_frame _ _ _ _ sameRow]
   rw [if_neg (by tauto)]
/-- Disjoint native word windows commute on the retained row, including
arbitrary untouched coordinates. No whole-row kernel evaluation. -/
theorem commute (row : Row) (i j : Fin 4) (x y : U64) (different : i≠j) :
 rowWrite (rowWrite row i x) j y=rowWrite (rowWrite row j y) i x := by
 apply Subtype.ext
 change (row.val.set i.val x).set j.val y=(row.val.set j.val y).set i.val x
 apply List.ext_getElem?
 intro k
 simp only [List.getElem?_set,List.length_set]
 have neq : i.val≠j.val := by intro h;exact different (Fin.ext h)
 by_cases hi : k=i.val <;> by_cases hj : k=j.val <;> simp_all [eq_comm]
#print axioms nested
#print axioms commute
end NBZ_WordFrame
