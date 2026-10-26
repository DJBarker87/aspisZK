import JFs_TX2_ArrayEight
import FIo_ReduceBounds
set_option autoImplicit false
namespace AspisR1.JFs_TX2_FoldLane
open Aeneas Aeneas.Std Result

def R : Nat := 10737418238

def lane (sums limbs : Array U64 8#usize) (j : Usize) : Result (Array U64 8#usize) := do
  let x ← Array.index_usize sums j
  let low ← lift (x &&& 2147483647#u64)
  let high ← x >>> 31#i32
  let folded ← low+high
  let before ← Array.index_usize limbs j
  let after ← before+folded
  Array.update limbs j after

theorem shift (x : U64) : x >>> 31#i32=ok (U64.wrapping_shr x 31#u32) := by rfl

theorem fold_bound (x : U64) : (FIo_ReduceBounds.fold x).val≤R := by
  unfold FIo_ReduceBounds.fold
  rw [UScalar.wrapping_add_val_eq,Nat.mod_eq_of_lt (FIo_ReduceBounds.sum_bound x)]
  have a:=FIo_ReduceFacts.low x
  have b:=FIo_ReduceBounds.shr_bound x
  unfold R
  omega

theorem source (sums limbs : Array U64 8#usize) (j : Usize) (x before : U64)
    (n : Nat) (hn : n<7) (hj : j.val<8)
    (hx : Array.index_usize sums j=ok x) (hb : Array.index_usize limbs j=ok before)
    (bound : before.val≤n*R) :
    ∃ out, lane sums limbs j=ok (limbs.set j out) ∧
      out.val=before.val+(FIo_ReduceBounds.fold x).val ∧ out.val≤(n+1)*R := by
  have small:=fold_bound x
  have total : before.val+(FIo_ReduceBounds.fold x).val≤UScalar.max .U64 := by
    norm_num [UScalar.max,UScalar.size,U64.numBits,UScalarTy.numBits,R] at *
    nlinarith
  obtain ⟨out,ho,vo⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=before) (y:=FIo_ReduceBounds.fold x) total)
  have write : Array.update limbs j out=ok (limbs.set j out) := by
    obtain ⟨a,ha,he⟩ := WP.spec_imp_exists (Array.update_spec limbs j out (by simpa [limbs.property] using hj))
    exact he ▸ ha
  refine ⟨out,?_,vo,?_⟩
  · simp only [lane,hx,hb,lift,bind_tc_ok,shift,FIo_ReduceBounds.checked,ho,write]
  · rw [vo];nlinarith

#print axioms shift
#print axioms fold_bound
#print axioms source
end AspisR1.JFs_TX2_FoldLane
