import NBZ_WordFrame
set_option autoImplicit false
namespace NBZ_Nested
open Aeneas Aeneas.Std Result
def arrayWrite {α : Type} {n : Usize} (row : Array α n) (k : Fin n.val) (value : α) : Array α n :=
 ⟨row.val.set k.val value,by simp only [List.length_set];exact row.property⟩
/-- The inverse-row carrier has five coordinates; raw rows have four. This
single law retains the actual Vec/Array types at either arity. -/
theorem array_nested {α : Type} {n : Usize} (raw : alloc.vec.Vec (Array α n))
 (index : Usize) (old : Array α n) (read : raw.val[index.val]?=some old)
 (k : Fin n.val) (value : α) (j l : Nat) :
 ((raw.set index (arrayWrite old k value)).val[j]?).bind (fun row=>row.val[l]?)=
 if j=index.val ∧ l=k.val then some value else (raw.val[j]?).bind (fun row=>row.val[l]?) := by
 have active : index.val<raw.val.length := by
   by_contra h
   rw [List.getElem?_eq_none (by omega)] at read
   cases read
 by_cases sameRow : j=index.val
 · subst j
   change ((raw.val.set index.val (arrayWrite old k value))[index.val]?).bind _=_
   rw [List.getElem?_set]
   simp only [active,if_pos,Option.bind_some,read,true_and]
   change (old.val.set k.val value)[l]?=_
   rw [List.getElem?_set]
   have inside : k.val<old.val.length := by rw [old.property];exact k.isLt
   by_cases sameWord : l=k.val
   · subst l;simp only [inside,if_pos]
   · simp only [if_neg sameWord,if_neg (Ne.symm sameWord)]
 · change ((raw.val.set index.val (arrayWrite old k value))[j]?).bind _=_
   rw [List.getElem?_set]
   simp only [if_neg sameRow,if_neg (Ne.symm sameRow)]
   rw [if_neg (by tauto)]
abbrev Q := NBF_RowInstall.Q
def word (q : Q) (k : Fin 4) : U32 :=
 match k.val with | 0=>q.c0.a | 1=>q.c0.b | 2=>q.c1.a | _=>q.c1.b
def write (q : Q) (k : Fin 4) (value : U32) : Q :=
 match k.val with
 | 0=>{q with c0:={q.c0 with a:=value}}
 | 1=>{q with c0:={q.c0 with b:=value}}
 | 2=>{q with c1:={q.c1 with a:=value}}
 | _=>{q with c1:={q.c1 with b:=value}}
/-- Native four-word QM31 access/set transports to the original cohort record,
without replacing its carrier by an independently selected tuple. -/
theorem word_write (q : Q) (k l : Fin 4) (value : U32) :
 word (write q k value) l=if l=k then value else word q l := by
 fin_cases k <;> fin_cases l <;> rfl
/-- Typed weight stores preserve the whole actual Vec and every exterior word. -/
theorem q_nested (raw : alloc.vec.Vec Q) (index : Usize) (old : Q)
 (read : raw.val[index.val]?=some old) (k l : Fin 4) (value : U32) (j : Nat) :
 ((raw.set index (write old k value)).val[j]?).map (fun q=>word q l)=
 if j=index.val ∧ l=k then some value else (raw.val[j]?).map (fun q=>word q l) := by
 have active : index.val<raw.val.length := by
   by_contra h
   rw [List.getElem?_eq_none (by omega)] at read
   cases read
 change ((raw.val.set index.val (write old k value))[j]?).map _=_
 rw [List.getElem?_set]
 by_cases same : j=index.val
 · subst j
   simp only [active,if_pos,Option.map_some,read,true_and,word_write]
   split <;> rfl
 · simp only [if_neg same,if_neg (Ne.symm same)]
   rw [if_neg (by tauto)]
#print axioms array_nested
#print axioms word_write
#print axioms q_nested
end NBZ_Nested
