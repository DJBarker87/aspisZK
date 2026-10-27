import XRp_ReversePass
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_RestoreChain
open XRp_ReverseStep XRp_ReverseBodies XRp_ReversePass

def appendIter (r : Iter) (xs : List U32)
    (h : (r.iter.slice.val ++ xs).length ≤ Usize.max) : Iter :=
  ⟨{r.iter with slice := ⟨r.iter.slice.val ++ xs,h⟩}⟩

theorem finish_append (n : Nat) (hn : n ≤ 7) (back : Back) (r : Iter)
    (hcap : (r.iter.slice.val ++ limbs n).length ≤ Usize.max) :
    finish n hn back r = back (appendIter r (limbs n) hcap) := by
  induction n generalizing back with
  | zero => simp [finish,restore,appendIter,limbs] at *; simp_all
  | succ n ih =>
    have hn' : n ≤ 7 := by omega
    have hlist : limbs (n+1) = limbs n ++ [0#u32] := by
      simp [limbs,List.replicate_succ']
    have hsmall : (r.iter.slice.val ++ limbs n).length ≤ Usize.max := by
      rw [hlist,List.length_append,List.length_append,List.length_singleton] at hcap
      simp only [List.length_append]
      omega
    rw [finish,ih hn' _ hsmall]
    simp only [restore,appendIter]
    have hnext : ((r.iter.slice.val ++ limbs n) ++ [0#u32]).length ≤ Usize.max := by
      simpa only [hlist,List.append_assoc] using hcap
    simp only [hnext, dite_true]
    congr 1
    apply congrArg (fun s : core.slice.iter.IterMut U32 => (⟨s⟩ : Iter))
    congr 1
    apply Subtype.ext
    exact (List.append_assoc _ _ _).trans (congrArg (r.iter.slice.val ++ ·) hlist.symm)

#print axioms finish_append
end XRp_RestoreChain
