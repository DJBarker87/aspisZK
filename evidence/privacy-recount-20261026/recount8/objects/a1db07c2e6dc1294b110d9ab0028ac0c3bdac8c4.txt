import R1Z.PV_RDB2C_PV_B2_C_251WideTotal
set_option autoImplicit false
namespace PV_B2_C_PowersBody
open Aeneas Aeneas.Std Result ControlFlow PV_B2_251c1
abbrev E := aspis_core.field.wide_exact.WideExact

theorem body_total {N : Usize} (x : E) (out : Array E N) (p : E) (i : Usize)
    (hi : i < N) : ∃ updated p1,
    prover_powers.powers_loop.body x out p i =
      ok (cont (updated,p1,Usize.wrapping_add i 1#usize)) := by
  obtain ⟨old,hr,_⟩ := WP.spec_imp_exists (Array.index_usize_spec out i (by
    change i.val < out.val.length
    rw [out.property]
    scalar_tac))
  unfold prover_powers.powers_loop.body
  simp only [hi,if_pos,Array.index_mut_usize,hr,bind_tc_ok,lift]
  split
  · simp only [PV_B2_C_251WideTotal.WideExact_mul,bind_tc_ok]
    exact ⟨_,_,rfl⟩
  · exact ⟨_,_,rfl⟩

theorem next_val {N : Usize} (i : Usize) (hi : i < N) :
    (Usize.wrapping_add i 1#usize).val = i.val+1 := by
  rw [Usize.wrapping_add_val_eq,Nat.mod_eq_of_lt]
  · rfl
  · have hn : N.val < UScalar.size .Usize := by
      simpa only [UScalar.val,UScalar.size,UScalarTy.numBits] using N.bv.isLt
    have hi' : i.val+1 ≤ N.val := by scalar_tac
    exact lt_of_le_of_lt hi' hn
#print axioms body_total
#print axioms next_val
end PV_B2_C_PowersBody
