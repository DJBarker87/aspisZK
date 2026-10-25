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
    let next : Usize := Usize.ofNatCore (j.val+1) (by scalar_tac)
    have nextval : next.val=j.val+1 := by simp [next]
    have add : j+1#usize=ok next := by
      change UScalar.tryMk .Usize (j.val+1)=_
      have hb : UScalar.inBounds .Usize (j.val+1) := by scalar_tac
      simp only [UScalar.tryMk,UScalar.tryMkOpt,
        dif_pos ((UScalar.check_bounds_eq_inBounds .Usize (j.val+1)).mpr hb),Result.ofOption]
      rfl
    unfold owned_contains_loop
    rw [loop.eq_def]
    simp only [owned_contains_loop.body,if_pos active,index,bind_tc_ok]
    by_cases hit : a.val[j.val]'(by have := a.property;scalar_tac)=candidate
    · simp only [if_pos hit,bind_tc_ok]
      exact ⟨some true,rfl⟩
    · simp only [if_neg hit,add,bind_tc_ok]
      exact ih next (by omega) (by omega)

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
