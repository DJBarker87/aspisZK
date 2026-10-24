import S9FactorArrayEntryV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9FactorNestedWriteV1
open AspisR1S9FactorArrayEntryV1

/-- Exact two-dimensional write/frame rule for the actual mutable-index
setter and row update. Generalizes the existing prepared-channel nested
set proof; later constructor loop invariants instantiate it at 5 by 5. -/
theorem accepted_nested_write
    {A : Type} {N M : Usize} (a : Array (Array A M) N)
    (i j k l : Usize) (row rowOut : Array A M)
    (back : Array A M → Array (Array A M) N) (x : A)
    (hi : i.val < N.val) (hj : j.val < M.val)
    (hk : k.val < N.val) (hl : l.val < M.val)
    (hmut : Array.index_mut_usize a i = .ok (row,back))
    (hupdate : Array.update row j x = .ok rowOut) :
    atN (atN (back rowOut) k hk) l hl =
      if k.val=i.val then
        if l.val=j.val then x else atN (atN a i hi) l hl
      else atN (atN a k hk) l hl := by
  have hread := index_atN a i hi
  unfold Array.index_mut_usize at hmut
  rw [hread,bind_tc_ok] at hmut
  have he := Result.ok.inj hmut
  have hrow : row = atN a i hi := (congrArg Prod.fst he).symm
  have hback : back = fun v => a.set i v := (congrArg Prod.snd he).symm
  have hout := accepted_update_eq_set row j hj x rowOut hupdate
  rw [hback,hout,atN_set a i k (row.set j x) hi hk]
  by_cases heq : k.val=i.val
  · simp only [if_pos heq]
    rw [atN_set row j l x hj hl,hrow]
  · simp only [if_neg heq]

#print axioms accepted_nested_write
end AspisR1S9FactorNestedWriteV1
