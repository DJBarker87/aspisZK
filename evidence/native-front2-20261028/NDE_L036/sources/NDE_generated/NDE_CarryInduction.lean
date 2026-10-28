import NDE_CarryStep
import RPv_FIy_Carry
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace NDE_CarryInduction
abbrev nativeLoop := FIq_Native.pool_v1.pair_forest_semantic_terminal.bounded_append_carry_loop

theorem loop_done {α β : Type} (body : α → Result (ControlFlow α β))
    (x : α) (y : β) (step : body x = ok (.done y)) : loop body x = ok y := by
  conv_lhs => unfold loop
  simp only [step]

theorem loop_continue {α β : Type} (body : α → Result (ControlFlow α β))
    (x next : α) (step : body x = ok (.cont next)) : loop body x = loop body next := by
  conv_lhs => unfold loop
  simp only [step]

theorem paired (fuel : Nat) (index : U64) (carry : Usize)
    (span : carry.val + fuel = 20) :
    ∃ out pending, NDE_Reference7.carry_ref_loop index carry = ok (out,pending) ∧
      (pending = none ∨ pending = some out) ∧ nativeLoop index carry = ok out := by
  induction fuel generalizing index carry with
  | zero =>
    have stop : ¬carry < 20#usize := by change ¬carry.val < 20; omega
    refine ⟨carry,none,?_,Or.inl rfl,?_⟩
    · unfold NDE_Reference7.carry_ref_loop
      apply loop_done
      simp only [NDE_Reference7.carry_ref_loop.body,stop,ite_false]
    · rw [nativeLoop,FIq_Native.pool_v1.pair_forest_semantic_terminal.bounded_append_carry_loop.eq_def,
        if_neg stop]
  | succ fuel ih =>
    have active : carry < 20#usize := by change carry.val < 20; omega
    by_cases even : (index &&& 1#u64) = 0#u64
    · refine ⟨carry,some carry,?_,Or.inr rfl,?_⟩
      · unfold NDE_Reference7.carry_ref_loop
        apply loop_done
        simp only [NDE_Reference7.carry_ref_loop.body,active,ite_true,lift,bind_tc_ok,even]
      · rw [nativeLoop,FIq_Native.pool_v1.pair_forest_semantic_terminal.bounded_append_carry_loop.eq_def,
          if_pos active]
        simp only [lift,bind_tc_ok,even,ite_true]
    · obtain ⟨nextIndex,shift,shiftSpec⟩ := WP.spec_imp_exists
        (UScalar.ShiftRight_spec index 1#u32 (by decide))
      have hmax := Usize.cMax_bound_concrete.1
      have addSpec : (carry + 1#usize : Result Usize) ⦃z => z.val = carry.val + 1⦄ := by
        apply UScalar.add_spec
        scalar_tac
      obtain ⟨nextCarry,increment,value⟩ := WP.spec_imp_exists addSpec
      obtain ⟨out,pending,refRun,returnValue,nativeRun⟩ :=
        ih nextIndex nextCarry (by omega)
      refine ⟨out,pending,?_,returnValue,?_⟩
      · unfold NDE_Reference7.carry_ref_loop at refRun ⊢
        rw [loop_continue _ _ (nextIndex,nextCarry) (by
          simp only [NDE_Reference7.carry_ref_loop.body,active,ite_true,lift,bind_tc_ok,
            if_neg even,shift,increment])]
        exact refRun
      · rw [nativeLoop,FIq_Native.pool_v1.pair_forest_semantic_terminal.bounded_append_carry_loop.eq_def,
          if_pos active]
        simp only [lift,bind_tc_ok,if_neg even,shift,increment]
        exact nativeRun

theorem carry_reference (index : U64) :
    NDE_Reference7.carry_ref index =
    FIq_Native.pool_v1.pair_forest_semantic_terminal.bounded_append_carry index := by
  obtain ⟨out,pending,refRun,returnValue,nativeRun⟩ := paired 20 index 0#usize (by rfl)
  unfold NDE_Reference7.carry_ref FIq_Native.pool_v1.pair_forest_semantic_terminal.bounded_append_carry
  rw [refRun]
  simp only [bind_tc_ok]
  rcases returnValue with rfl | rfl <;> exact nativeRun.symm

#print axioms loop_done
#print axioms loop_continue
#print axioms paired
#print axioms carry_reference
end NDE_CarryInduction
