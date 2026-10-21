import MultiproofConeSortInsertion

set_option autoImplicit false
namespace AspisR1.MultiproofConeSortTotal
open Aeneas Aeneas.Std Result MultiproofSortRef
open AspisR1.MultiproofConeSortInsertion

/-- Exact insertion, including permutation and every suffix beyond the cursor. -/
theorem insert_prefix_total (keys : Array U64 16#usize) (cursor : Usize)
    (bound : cursor.val<16)
    (sorted : (keys.val.take cursor.val).Pairwise (· ≤ ·)) :
    ∃ out, sort_reference.insert_rows keys cursor = ok out ∧
      out.val.Perm keys.val ∧
      (out.val.take (cursor.val+1)).Pairwise (· ≤ ·) ∧
      ∀ k, cursor.val+1≤k → out.val.drop k=keys.val.drop k := by
  have len : keys.val.length=16 := keys.property
  have inbounds : cursor.val<keys.val.length := by omega
  let pre := keys.val.take cursor.val
  let x := keys.val[cursor.val]!
  let tail := keys.val.drop (cursor.val+1)
  have shape : keys.val=pre++x::tail := by
    dsimp [pre,x,tail]
    rw [getElem!_pos keys.val cursor.val inbounds]
    exact (List.take_append_drop cursor.val keys.val).symm.trans
      (congrArg (fun t => keys.val.take cursor.val ++ t) (List.drop_eq_getElem_cons inbounds))
  have plen : pre.length=cursor.val := by simp [pre];omega
  obtain ⟨out, eqout, content⟩ := insert_rows_total pre.reverse x tail keys cursor
    (by simpa using shape) (by simpa using plen.symm)
  have perm := (List.reverse_perm (insertReverse pre.reverse x)).trans
    ((insertReverse_perm pre.reverse x).trans (List.reverse_perm (x::pre.reverse)).symm)
  have blockperm : (insertReverse pre.reverse x).reverse |>.Perm (pre++[x]) := by
    simpa using perm
  have blocklen : ((insertReverse pre.reverse x).reverse).length=cursor.val+1 := by
    have := blockperm.length_eq
    simpa [plen] using this
  refine ⟨out,eqout,?_,?_,?_⟩
  · rw [content,shape]
    simpa [List.append_assoc] using blockperm.append_right tail
  · have desc : pre.reverse.Pairwise (fun a b => b ≤ a) := by
      simpa [List.pairwise_reverse] using sorted
    have asc := insertReverse_sorted pre.reverse x desc
    rw [content,←blocklen,List.take_left]
    simpa [List.pairwise_reverse] using asc
  · intro k hk
    rw [content,shape,List.drop_append, List.drop_append]
    have p : k≥pre.length := by omega
    have q : k≥((insertReverse pre.reverse x).reverse).length := by omega
    simp only [List.drop_eq_nil_iff.mpr q, List.drop_eq_nil_iff.mpr p,
      List.nil_append, blocklen,plen]
    have kp : k-cursor.val = (k-(cursor.val+1))+1 := by omega
    rw [kp,List.drop_succ_cons]

/-- The two actual extracted recurrences terminate on the entire bounded
array domain. The live prefix is sorted; scratch beyond n is unchanged. -/
theorem sort_rows_total (fuel : Nat) (keys : Array U64 16#usize)
    (cursor n : Usize) (range : cursor.val+fuel=n.val) (bound : n.val≤16)
    (sorted : (keys.val.take cursor.val).Pairwise (· ≤ ·)) :
    ∃ out, sort_reference.sort_rows keys cursor n = ok out ∧
      out.val.Perm keys.val ∧ (out.val.take n.val).Pairwise (· ≤ ·) ∧
      out.val.drop n.val=keys.val.drop n.val := by
  induction fuel generalizing keys cursor with
  | zero =>
    have stop : cursor≥n := by change cursor.val≥n.val;omega
    rw [sort_reference.sort_rows]
    simp only [stop,if_true]
    exact ⟨keys,rfl,List.Perm.refl _,by simpa [show cursor.val=n.val by omega] using sorted,rfl⟩
  | succ fuel ih =>
    have cb : cursor.val<16 := by omega
    have more : ¬cursor≥n := by change ¬cursor.val≥n.val;omega
    obtain ⟨next,eqnext,perm,sortedNext,suffix⟩ := insert_prefix_total keys cursor cb sorted
    have add := UScalar.add_spec (x:=cursor) (y:=1#usize) (by scalar_tac)
    obtain ⟨succ,eqsucc,succval⟩ := WP.spec_imp_exists add
    have sv : succ.val=cursor.val+1 := by scalar_tac
    obtain ⟨out,eqout,operm,osorted,osuffix⟩ := ih next succ (by omega)
      (by simpa [sv] using sortedNext)
    refine ⟨out,?_,operm.trans perm,osorted,osuffix.trans (suffix _ (by omega))⟩
    rw [sort_reference.sort_rows]
    simp only [more,if_false,eqnext,bind_tc_ok,eqsucc]
    exact eqout

/-- The returned prefix is the unique ascending permutation, hence exactly
Lean core's frozen merge-sort construction on packed keys. -/
theorem sort_eq_mergeSort (keys : Array U64 16#usize) (n : Usize) (bound : n.val≤16) :
    ∃ out, sort_reference.sort_rows keys 0#usize n=ok out ∧
      out.val.take n.val=(keys.val.take n.val).mergeSort (fun a b => decide (a≤b)) ∧
      out.val.drop n.val=keys.val.drop n.val := by
  obtain ⟨out,eqout,perm,sorted,suffix⟩ := sort_rows_total n.val keys 0#usize n (by simp) bound (by simp)
  have p : (out.val.take n.val).Perm (keys.val.take n.val) := by
    have split := perm
    rw [←List.take_append_drop n.val out.val,←List.take_append_drop n.val keys.val,suffix] at split
    exact (List.perm_append_right_iff (keys.val.drop n.val)).mp split
  have ms := List.pairwise_mergeSort (le:=fun a b : U64 => decide (a≤b))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *;scalar_tac)
    (by intro a b; simp only [Bool.or_eq_true,decide_eq_true_eq];scalar_tac)
    (keys.val.take n.val)
  refine ⟨out,eqout,?_,suffix⟩
  apply List.Perm.eq_of_pairwise (le:=fun a b : U64 => a≤b)
    (fun a b _ _ hab hba => by apply UScalar.eq_of_val_eq;scalar_tac) sorted
    (by simpa only [decide_eq_true_eq] using ms)
  exact p.trans (List.mergeSort_perm _ _).symm

#print axioms insert_prefix_total
#print axioms sort_rows_total
#print axioms sort_eq_mergeSort
end AspisR1.MultiproofConeSortTotal
