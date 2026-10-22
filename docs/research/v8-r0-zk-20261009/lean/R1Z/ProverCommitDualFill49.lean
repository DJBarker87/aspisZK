import AspisR1ProducerRelease47.Dual49
import R1Z.ProverCommitDualCell48
import R1Z.ProverCommitFoldValue48
/-! Complete source-owned dual fold interval, using the retained exact cell. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitDualFill49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitFoldRange48

def cellValue (q : Nat → Raw) (a : Exact) (i : Nat) : Exact :=
  ProverCommitDualCell48.polynomial (fun j => q (4*i+j)) a

attribute [local irreducible] sourceArray source value ProverCommitDualCell48.polynomial

theorem fill (q : Nat → Raw) (hq : ∀ k, k < 1024 → canonical (q k))
    (a : Raw) (ha : canonical a) (n : Nat) (xs : Nat → Raw)
    (hxs : ∀ k, k < 256 → canonical (xs k))
    (i : Usize) (left : U16) (hleft : left.val=n) (bound : i.val+n ≤ 256) :
    ∃ ys : Nat → Raw,
      dual.first (sourceArray 1024#usize q) (source a) (sourceArray 256#usize xs) i left=
        ok (sourceArray 256#usize ys) ∧
      (∀ k, k < 256 → canonical (ys k)) ∧
      ∀ k, k < 256 → value (ys k)=if i.val  ≤  k ∧ k < i.val+n then cellValue q (value a) k else value (xs k) := by
  induction n generalizing xs i left with
  | zero =>
    have hz : left=0#u16 := by scalar_tac
    refine ⟨xs,?_,hxs,?_⟩
    · rw [dual.first,hz];rfl
    · intro k hk;rw [if_neg (by omega)]
  | succ n ih =>
    have hi : i.val < 256 := by omega
    have h0 : (Usize.wrapping_mul 4#usize i).val=4*i.val := four_val i hi
    have h1 : (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) 1#usize).val=4*i.val+1 := offset_val i hi _ (by decide)
    have h2 : (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) 2#usize).val=4*i.val+2 := offset_val i hi _ (by decide)
    have h3 : (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) 3#usize).val=4*i.val+3 := offset_val i hi _ (by decide)
    have hn : left≠0#u16 := by scalar_tac
    have hdec : (U16.wrapping_sub left 1#u16).val=n := by
      rw [ProverCommitPairCounter47.sub_one left (by omega)];omega
    have hinc : (Usize.wrapping_add i 1#usize).val=i.val+1 := ProverCommitPairCounter47.next_val i (by omega)
    let chunk : Nat → Raw := fun j => q (4*i.val+j)
    obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitDualCell48.cell chunk (fun j hj => hq _ (by omega)) a ha
    let next := Function.update xs i.val z
    have hcnext : ∀ k, k < 256 → canonical (next k) := by
      intro k hk
      by_cases he : k=i.val
      · subst k;simpa only [next,Function.update_self] using hcz
      · simpa only [next,Function.update_of_ne he] using hxs k hk
    obtain ⟨ys,hy,hcy,hdys⟩ := ih next hcnext _ _ hdec (by rw [hinc];omega)
    refine ⟨ys,?_,hcy,?_⟩
    · rw [dual.first]
      simp only [hn,if_false,lift,bind_tc_ok]
      rw [index 1024#usize q _ (by rw [h0];change 4*i.val < 1024;omega)]
      simp only [bind_tc_ok,h0]
      rw [index 1024#usize q _ (by rw [h1];change 4*i.val+1 < 1024;omega)]
      simp only [bind_tc_ok,h1]
      rw [index 1024#usize q _ (by rw [h2];change 4*i.val+2 < 1024;omega)]
      simp only [bind_tc_ok,h2]
      rw [index 1024#usize q _ (by rw [h3];change 4*i.val+3 < 1024;omega)]
      simp only [bind_tc_ok,h3]
      have hc : Array.make 4#usize [source (q (4*i.val)),source (q (4*i.val+1)),
          source (q (4*i.val+2)),source (q (4*i.val+3))]=sourceArray 4#usize chunk := by
        simpa only [chunk,Nat.add_zero] using four_array chunk
      rw [hc,hz]
      simp only [bind_tc_ok]
      rw [ProverCommitWideArray48.update 256#usize xs i (by change i.val < 256;exact hi) z]
      simp only [bind_tc_ok]
      exact hy
    · intro k hk
      rw [hdys k hk,hinc]
      by_cases he : k=i.val
      · rw [if_neg (by omega),if_pos (by omega)]
        simp only [next,he,Function.update_self]
        exact hdz
      · by_cases ht : i.val+1  ≤  k ∧ k < i.val+1+n
        · rw [if_pos ht,if_pos (by omega)]
        · rw [if_neg ht,if_neg (by omega)]
          simp only [next,Function.update_of_ne he]

#print axioms fill
end R1Z.ProverCommitDualFill49
