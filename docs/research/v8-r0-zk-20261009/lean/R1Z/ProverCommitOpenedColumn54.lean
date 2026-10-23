import AspisR1ProducerRelease47.EncoderLeaves54
import R1Z.ProverCommitWideArray48
import R1Z.ProverCommitArray49
/-! Exact row/column storage of all four opened values. This proof is
independent of the field computations that produced the four values. -/
set_option autoImplicit false
namespace R1Z.ProverCommitOpenedColumn54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48

def matrix (xs : Nat → Nat → Raw) : Array (Array Source 29#usize) 4#usize :=
  ProverCommitArray49.array 4#usize (fun s => sourceArray 29#usize (xs s))

theorem set_from_update {A : Type} {n : Usize} (a b : Array A n) (i : Usize) (x : A)
    (hi : i.val<a.val.length) (h : Array.update a i x=ok b) : Aeneas.Std.Array.set a i x=b := by
  obtain ⟨out,hout,hset⟩ := WP.spec_imp_exists (Array.update_spec a i x hi)
  have he : b=out := Result.ok.inj (h.symm.trans hout)
  exact hset.symm.trans he.symm

theorem set_row (xs : Nat → Nat → Raw) (s : Usize) (hs : s.val<4) (row : Nat → Raw) :
    Aeneas.Std.Array.set (matrix xs) s (sourceArray 29#usize row)=matrix (Function.update xs s.val row) := by
  have hu := ProverCommitArray49.update 4#usize (fun s => sourceArray 29#usize (xs s)) s hs
    (sourceArray 29#usize row)
  have hset := set_from_update _ _ s _ (by simp only [ProverCommitArray49.array,List.length_ofFn];exact hs) hu
  rw [matrix,hset,matrix]
  congr 1
  funext t
  by_cases he : t=s.val
  · subst t;simp only [Function.update_self]
  · simp only [Function.update_of_ne he]

attribute [local irreducible] matrix sourceArray source

theorem column (h : Nat → Raw) (l s : Usize) (hl : l.val<29) (n : Nat)
    (left : U8) (hleft : left.val=n) (bound : s.val+n≤4) (xs : Nat → Nat → Raw) :
    ∃ out : Nat → Nat → Raw,
      leaves54.column (matrix xs) (sourceArray 4#usize h) l s left=ok (matrix out) ∧
      ∀ r c, r<4 → c<29 → out r c=
        if s.val ≤ r ∧ r<s.val+n ∧ c=l.val then h r else xs r c := by
  induction n generalizing s left xs with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    refine ⟨xs,?_,?_⟩
    · rw [leaves54.column,hz];rfl
    · intro r c hr hc;rw [if_neg (by omega)]
  | succ n ih =>
    have hne : left≠0#u8 := by scalar_tac
    have hs : s.val<4 := by omega
    have hdec : (U8.wrapping_sub left 1#u8).val=n := by
      rw [ProverCommitBasisCounter47.sub_one left (by omega)];omega
    have hinc : (Usize.wrapping_add s 1#usize).val=s.val+1 :=
      ProverCommitPairCounter47.next_val s (by omega)
    let next := Function.update xs s.val (Function.update (xs s.val) l.val (h s.val))
    obtain ⟨out,hout,hdout⟩ := ih (Usize.wrapping_add s 1#usize) _ hdec (by rw [hinc];omega) next
    refine ⟨out,?_,?_⟩
    · rw [leaves54.column]
      simp only [hne,if_false,index 4#usize h s hs,Array.index_mut_usize,bind_tc_ok]
      have hrow : Array.index_usize (matrix xs) s=ok (sourceArray 29#usize (xs s.val)) :=
        by unfold matrix;exact ProverCommitArray49.index 4#usize (fun r => sourceArray 29#usize (xs r)) s hs
      rw [hrow];simp only [bind_tc_ok]
      change (do
        let row ← Array.update (sourceArray 29#usize (xs s.val)) l (source (h s.val))
        leaves54.column (Aeneas.Std.Array.set (matrix xs) s row) (sourceArray 4#usize h) l
          (Usize.wrapping_add s 1#usize) (U8.wrapping_sub left 1#u8))=ok (matrix out)
      rw [ProverCommitWideArray48.update 29#usize (xs s.val) l hl (h s.val)]
      simp only [bind_tc_ok,lift]
      rw [set_row xs s hs]
      exact hout
    · intro r c hr hc
      rw [hdout r c hr hc,hinc]
      by_cases he : r=s.val
      · subst r
        rw [if_neg (by omega)]
        simp only [next,Function.update_self]
        by_cases hcol : c=l.val
        · subst c;rw [Function.update_self,if_pos (by omega)]
        · rw [Function.update_of_ne hcol,if_neg (by omega)]
      · by_cases ht : s.val+1 ≤ r ∧ r<s.val+1+n ∧ c=l.val
        · rw [if_pos ht,if_pos (by omega)]
        · rw [if_neg ht,if_neg (by omega)]
          simp only [next,Function.update_of_ne he]

#print axioms set_from_update
#print axioms set_row
#print axioms column
end R1Z.ProverCommitOpenedColumn54
