import S1OwnedQueryBlockFunsV1
import S1QueryArrayOperationsV1
set_option autoImplicit false
namespace AspisS1OwnedQueryBlock.Total
open Aeneas Aeneas.Std Result ControlFlow

/-- TOTAL on the admitted prefix domain; arbitrary duplicate/full raw U32 values.
This proves termination and absence of extracted arithmetic/index failures. -/
theorem contains_loop_total (fuel : Nat) (a : Array U32 22#usize)
    (len : Usize) (candidate : U32) (j : Usize)
    (hlen : len.val ≤ 22) (hj : j.val ≤ len.val) (hf : len.val-j.val=fuel) :
    ∃ out, owned_contains_loop a len candidate j=ok out := by
  induction fuel generalizing j with
  | zero =>
    have stop : ¬ j < len := by scalar_tac
    unfold owned_contains_loop
    rw [loop.eq_def]
    simp only [owned_contains_loop.body,if_neg stop,bind_tc_ok]
    exact ⟨none,rfl⟩
  | succ fuel ih =>
    have active : j < len := by scalar_tac
    have index := AspisS1QueryArrayOperations.index_total a j (by scalar_tac)
    have jbound : j.val+1≤Usize.max := by have := Usize.hmax; omega
    have add : j+1#usize=ok (Usize.ofNatCore (j.val+1) jbound) := by scalar_tac
    unfold owned_contains_loop
    rw [loop.eq_def]
    simp only [owned_contains_loop.body,if_pos active,index,bind_tc_ok]
    split
    · exact ⟨some true,rfl⟩
    · simp only [add,bind_tc_ok]
      exact ih _ (by simp only [Usize.ofNatCore_val];omega)
        (by simp only [Usize.ofNatCore_val];omega)

theorem contains_total (a : Array U32 22#usize) (len : Usize) (candidate : U32)
    (hlen : len.val≤22) : ∃ out, owned_contains a len candidate=ok out := by
  obtain ⟨out,call⟩ := contains_loop_total len.val a len candidate 0#usize hlen
    (by scalar_tac) (by scalar_tac)
  unfold owned_contains
  rw [call]
  cases out with
  | none => exact ⟨false,rfl⟩
  | some b => exact ⟨b,rfl⟩

#print axioms contains_loop_total
#print axioms contains_total
end AspisS1OwnedQueryBlock.Total
