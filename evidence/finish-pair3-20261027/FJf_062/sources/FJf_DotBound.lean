import FJf_DotPushValue
import JFs_TX2_FoldLane
set_option autoImplicit false
namespace AspisR1.FJf_DotBound
open Aeneas Aeneas.Std Result
open FJf_DotLane (Dot model)
open FJf_U64Array (cell)

def Bound (dot : Dot) (n : Nat) : Prop := ∀ j,j < 4 → (cell dot.sums j).val≤n*JFs_TX2_FoldLane.R

theorem addition (before raw : U64) (n : Nat) (hn : n < 4096)
    (hb : before.val≤n*JFs_TX2_FoldLane.R) :
    (U64.wrapping_add before (FIo_ReduceBounds.fold raw)).val=
      before.val+(FIo_ReduceBounds.fold raw).val ∧
    (U64.wrapping_add before (FIo_ReduceBounds.fold raw)).val≤(n+1)*JFs_TX2_FoldLane.R := by
  have hf := JFs_TX2_FoldLane.fold_bound raw
  have small : before.val+(FIo_ReduceBounds.fold raw).val < UScalar.size .U64 := by
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits,JFs_TX2_FoldLane.R] at hb hf ⊢
    nlinarith
  rw [U64.wrapping_add_val_eq,Nat.mod_eq_of_lt small]
  exact ⟨rfl,by nlinarith⟩

theorem push (dot out : Dot) (a b : FIo_Native.fast_pairing.canonical.Q)
    (n : Nat) (hn : n < 4096) (bound : Bound dot n)
    (run : FIo_Native.fast_pairing.canonical.Dot.push dot a b=ok out) :
    ∃ raw,FIo_Native.fast_pairing.canonical.Q.raw a b=ok raw ∧ Bound out (n+1) ∧
      ∀ j,j < 4 → (cell out.sums j).val=
        (cell dot.sums j).val+(FIo_ReduceBounds.fold (cell raw j)).val := by
  obtain ⟨raw,hr,hv⟩ := FJf_DotPushValue.source dot out a b run
  refine ⟨raw,hr,?_,?_⟩
  · intro j hj
    rw [hv j hj]
    exact (addition _ _ n hn (bound j hj)).2
  · intro j hj
    rw [hv j hj]
    exact (addition _ _ n hn (bound j hj)).1
#print axioms addition
#print axioms push
end AspisR1.FJf_DotBound
