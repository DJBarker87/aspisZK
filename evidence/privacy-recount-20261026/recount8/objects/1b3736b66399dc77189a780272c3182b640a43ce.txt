import AspisR1ProducerRelease47.Powers48
import R1Z.ProverCommitWideArray48
import R1Z.ProverCommitBasisCounter47
/-! Exact native power-array owner, including the final iteration's early
return (no extra multiplication). Gamma and kappa use the same induction. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitPowers48
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48

theorem set_source (size : Usize) (xs : Nat → Raw) (i : Usize) (z : Raw) :
    Aeneas.Std.Array.set (sourceArray size xs) i (source z)=sourceArray size (Function.update xs i.val z) := by
  apply Subtype.ext
  change (sourceArray size xs).val.set i.val (source z)=
    (sourceArray size (Function.update xs i.val z)).val
  apply List.ext_getElem
  · simp only [List.length_set,sourceArray,List.length_ofFn]
  · intro k hk1 hk2
    simp only [sourceArray,List.getElem_set,List.getElem_ofFn]
    by_cases h : k=i.val
    · subst k;simp only [Function.update_self,if_true]
    · simp only [Ne.symm h,if_false,Function.update_of_ne h]

attribute [local irreducible] sourceArray source value

theorem fill_value (size : Usize) (capacity : size.val ≤ 256)
    (xs : Nat → Raw) (hxs : ∀ k, k < size.val → canonical (xs k))
    (x p : Raw) (hx : canonical x) (hp : canonical p)
    (n : Nat) (left : U8) (hleft : left.val=n) (i : Usize) (bound : i.val+n ≤ size.val) :
    ∃ ys : Nat → Raw,
      power_fill (sourceArray size xs) (source x) (source p) i left=ok (sourceArray size ys) ∧
      (∀ k, k < size.val → canonical (ys k)) ∧
      ∀ k, k < size.val → value (ys k)=
        if i.val ≤ k ∧ k < i.val+n then value p*(value x)^(k-i.val) else value (xs k) := by
  induction n generalizing xs p left i with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    refine ⟨xs,?_,hxs,?_⟩
    · rw [power_fill,hz];rfl
    · intro k hk;rw [if_neg (by omega)]
  | succ n ih =>
    have hi : i.val < size.val := by omega
    have hn : left≠0#u8 := by scalar_tac
    let next := Function.update xs i.val p
    have hcnext : ∀ k, k < size.val → canonical (next k) := by
      intro k hk
      by_cases he : k=i.val
      · subst k;simpa only [next,Function.update_self] using hp
      · simpa only [next,Function.update_of_ne he] using hxs k hk
    by_cases nz : n=0
    · subst n
      have hlast : left=1#u8 := by scalar_tac
      refine ⟨next,?_,hcnext,?_⟩
      · rw [power_fill]
        simp only [hlast,if_false,if_true,Array.index_mut_usize,index _ _ i hi,bind_tc_ok]
        change ok (Aeneas.Std.Array.set (sourceArray size xs) i (source p))=ok (sourceArray size next)
        rw [set_source]
      · intro k hk
        by_cases he : k=i.val
        · subst k
          rw [if_pos (by omega)]
          simp only [next,Function.update_self,Nat.sub_self,pow_zero,mul_one]
        · rw [if_neg (by omega)];simp only [next,Function.update_of_ne he]
    · have hmore : left≠1#u8 := by scalar_tac
      have hdec : (U8.wrapping_sub left 1#u8).val=n := by
        rw [ProverCommitBasisCounter47.sub_one left (by omega)];omega
      have hinc : (Usize.wrapping_add i 1#usize).val=i.val+1 := ProverCommitPairCounter47.next_val i (by omega)
      obtain ⟨product,hprod,hcprod,hdprod⟩ := mul_exact p x hp hx
      obtain ⟨ys,hy,hcy,hval⟩ := ih next hcnext product hcprod _ hdec
        (Usize.wrapping_add i 1#usize) (by rw [hinc];omega)
      refine ⟨ys,?_,hcy,?_⟩
      · rw [power_fill]
        simp only [hn,if_false,Array.index_mut_usize,index _ _ i hi,bind_tc_ok,hmore,hprod,lift]
        change power_fill (Aeneas.Std.Array.set (sourceArray size xs) i (source p))
          (source x) (source product) (Usize.wrapping_add i 1#usize)
          (U8.wrapping_sub left 1#u8)=ok (sourceArray size ys)
        rw [set_source]
        exact hy
      · intro k hk
        rw [hval k hk,hinc]
        by_cases he : k=i.val
        · have ht : ¬(i.val+1 ≤ k ∧ k < i.val+1+n) := by omega
          rw [if_neg ht,if_pos (by omega)]
          simp only [next,he,Function.update_self,Nat.sub_self,pow_zero,mul_one]
        · by_cases ht : i.val+1 ≤ k ∧ k < i.val+1+n
          · rw [if_pos ht,if_pos (by omega),hdprod]
            have ex : k-i.val=(k-(i.val+1))+1 := by omega
            rw [ex,pow_succ]
            ring
          · rw [if_neg ht,if_neg (by omega)]
            simp only [next,Function.update_of_ne he]

#print axioms set_source
#print axioms fill_value
end R1Z.ProverCommitPowers48
