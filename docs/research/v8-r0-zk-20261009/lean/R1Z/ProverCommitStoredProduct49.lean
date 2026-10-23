import AspisR1ProducerRelease47.Stored49
import R1Z.ProverCommitCircleRows49
import R1Z.ProverCommitWeightDigit49
import R1Z.ProverCommitFactorProduct49
/-! Actual stored matrix reads and source shift/mask digits feed the already
proved five-factor product. No factor-array image is assumed. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitStoredProduct49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitCircleRows49

def selected (rows : Nat → Nat → Old.Q) (j : Usize) (d : Nat) : Old.Q :=
  rows d ((j.val/4^d)%4)

theorem matrix_index (rows : Nat → Nat → Old.Q) (d : Usize) (hd : d.val<5) :
    Array.index_usize (matrix rows) d=ok (ProverCommitQArray48.array 4#usize (rows d.val)) := by
  rw [matrix,ProverCommitArray49.index _ _ _ hd]

attribute [local irreducible] matrix ProverCommitQArray48.array ProverCommitNativeQ48.source

theorem binding (rows : Nat → Nat → Old.Q) (j : Usize) (n : Nat)
    (d : Usize) (left : U8) (hleft : left.val=n) (bound : d.val+n≤5) (acc : field.QM31) :
    stored.product (matrix rows) j d left acc=
      factors.product (ProverCommitQArray48.array 5#usize (selected rows j)) d left acc := by
  induction n generalizing d left acc with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    rw [stored.product,factors.product,hz];rfl
  | succ n ih =>
    have hn : left≠0#u8 := by scalar_tac
    have hd : d.val<5 := by omega
    have hdec : (U8.wrapping_sub left 1#u8).val=n := by
      rw [ProverCommitBasisCounter47.sub_one left (by omega)];omega
    have hinc : (Usize.wrapping_add d 1#usize).val=d.val+1 := by
      simpa only [show (1#usize).val=1 from rfl] using
        ProverCommitBasisFillValue47.add_val d 1#usize (by change d.val+1<2048;omega)
    let digit := (Usize.wrapping_shr j (UScalar.cast .U32 (Usize.wrapping_mul 2#usize d))) &&& 3#usize
    have hdigit : digit.val=(j.val/4^d.val)%4 := ProverCommitWeightDigit49.digit j d hd
    have hdigitbound : digit.val<4 := by rw [hdigit];exact Nat.mod_lt _ (by decide)
    have ht : ∀ a, stored.product (matrix rows) j (Usize.wrapping_add d 1#usize) (U8.wrapping_sub left 1#u8) a=
        factors.product (ProverCommitQArray48.array 5#usize (selected rows j)) (Usize.wrapping_add d 1#usize) (U8.wrapping_sub left 1#u8) a :=
      fun a => ih _ _ hdec (by rw [hinc];omega) a
    rw [stored.product,factors.product]
    simp only [hn,if_false,lift,bind_tc_ok,matrix_index rows d hd]
    change (do
      let q ← Array.index_usize (ProverCommitQArray48.array 4#usize (rows d.val)) digit
      let next ← field.QM31.mul acc q
      stored.product (matrix rows) j (Usize.wrapping_add d 1#usize) (U8.wrapping_sub left 1#u8) next)=_
    rw [ProverCommitQArray48.index _ _ _ hdigitbound,ProverCommitQArray48.index _ _ _ hd]
    simp only [bind_tc_ok,ht,selected,hdigit]

#print axioms matrix_index
#print axioms binding
end R1Z.ProverCommitStoredProduct49
