import AspisR1ProducerRelease47.Materialization49
import R1Z.ProverCommitWeightOutput49
import R1Z.ProverCommitWideArray48
import R1Z.ProverCommitArray49
/-! Full materialization interval induction over stored raw rows. The source
kappa array is immutable and every other output slot is preserved. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitMaterialFill49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitWeightSum49

def table (raw : Nat → Nat → Old.Q) : Array (Array field.QM31 7#usize) 1024#usize :=
  ProverCommitArray49.array 1024#usize (fun j => ProverCommitQArray48.array 7#usize (raw j))

theorem table_index (raw : Nat → Nat → Old.Q) (j : Usize) (hj : j.val<1024) :
    Array.index_usize (table raw) j=ok (ProverCommitQArray48.array 7#usize (raw j.val)) := by
  rw [table,ProverCommitArray49.index _ _ _ hj]

attribute [local irreducible] table sourceArray source value ProverCommitQArray48.array

theorem fill (kp : Nat → Raw) (hkp : ∀ i, i<7 → canonical (kp i))
    (raw : Nat → Nat → Old.Q) (n : Nat) (xs : Nat → Raw)
    (hxs : ∀ i, i<1024 → canonical (xs i))
    (j : Usize) (left : U16) (hleft : left.val=n) (bound : j.val+n≤1024) :
    ∃ out : Nat → Raw,
      materialization.fill (sourceArray 7#usize kp) (table raw) (sourceArray 1024#usize xs) j left=
        ok (sourceArray 1024#usize out) ∧
      (∀ i, i<1024 → canonical (out i)) ∧
      ∀ i, i<1024 → value (out i)=
        if j.val ≤ i ∧ i<j.val+n then value (xs i)+terms kp (raw i) 7 0 else value (xs i) := by
  induction n generalizing xs j left with
  | zero =>
    have hz : left=0#u16 := by scalar_tac
    refine ⟨xs,?_,hxs,?_⟩
    · rw [materialization.fill,hz];rfl
    · intro i hi;rw [if_neg (by omega)]
  | succ n ih =>
    have hn : left≠0#u16 := by scalar_tac
    have hj : j.val<1024 := by omega
    have hdec : (U16.wrapping_sub left 1#u16).val=n := by
      rw [ProverCommitPairCounter47.sub_one left (by omega)];omega
    have hinc : (Usize.wrapping_add j 1#usize).val=j.val+1 := by
      simpa only [show (1#usize).val=1 from rfl] using
        ProverCommitBasisFillValue47.add_val j 1#usize (by change j.val+1<2048;omega)
    obtain ⟨v,hv,hcv,hdv⟩ := finite_value 7#usize (by decide) kp (raw j.val) hkp
      7 0#usize (by decide) (xs j.val) (hxs j.val hj)
    have hcell : owned.cell (sourceArray 7#usize kp) (ProverCommitQArray48.array 7#usize (raw j.val))
        0#usize 7#u8 (source (xs j.val))=ok (source v) := by
      rw [cell_finite 7 7#u8 rfl];exact hv
    let changed := Function.update xs j.val v
    have hc : ∀ i, i<1024 → canonical (changed i) := by
      intro i hi
      by_cases he : i=j.val
      · subst i;simpa only [changed,Function.update_self] using hcv
      · simpa only [changed,Function.update_of_ne he] using hxs i hi
    obtain ⟨out,hout,hcout,hdout⟩ := ih changed hc _ _ hdec (by rw [hinc];omega)
    refine ⟨out,?_,hcout,?_⟩
    · rw [materialization.fill]
      simp only [hn,if_false,table_index raw j hj,bind_tc_ok]
      rw [ProverCommitMix48.index _ _ _ hj]
      simp only [hcell,bind_tc_ok]
      rw [ProverCommitWideArray48.update _ _ _ hj v]
      simp only [lift,bind_tc_ok]
      exact hout
    · intro i hi
      rw [hdout i hi,hinc]
      by_cases he : i=j.val
      · subst i
        rw [if_neg (by omega),if_pos (by omega)]
        simpa only [changed,Function.update_self,show (0#usize).val=0 from rfl] using hdv
      · by_cases ht : j.val+1 ≤ i ∧ i<j.val+1+n
        · rw [if_pos ht,if_pos (by omega)]
          simp only [changed,Function.update_of_ne he]
        · rw [if_neg ht,if_neg (by omega)]
          simp only [changed,Function.update_of_ne he]

#print axioms table_index
#print axioms fill
end R1Z.ProverCommitMaterialFill49
