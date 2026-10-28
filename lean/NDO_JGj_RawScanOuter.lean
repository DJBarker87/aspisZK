import NDO_JGj_RawScan
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_RawScanOuter
open Aeneas Aeneas.Std Result WP FIq_Native
theorem source (n : Nat) (table : JGj_RawScan.Table) (flag : Bool) (row : Usize)
    (hn : row.val+n=4) :
    state_only_poseidon.external_local_packed_raw_loop0 table flag row=ok () := by
  induction n generalizing row flag with
  | zero =>
    have h : ¬row<4#usize := by scalar_tac
    rw [state_only_poseidon.external_local_packed_raw_loop0.eq_def,if_neg h]
  | succ n ih =>
    have h : row<4#usize := by scalar_tac
    have hr : row.val<4 := by omega
    obtain ⟨flag1,rf⟩ := JGj_RawScan.inner 4 table flag row 0#usize hr rfl
    have spec : (row+1#usize : Result Usize) ⦃ next=>next.val=row.val+1 ⦄ := by
      apply UScalar.add_spec
      scalar_tac
    obtain ⟨next,rn,vn⟩ := WP.spec_imp_exists spec
    rw [state_only_poseidon.external_local_packed_raw_loop0.eq_def,if_pos h,rf,bind_tc_ok,rn,bind_tc_ok]
    exact ih flag1 next (by omega)
#print axioms source
end AspisR1.JGj_RawScanOuter
end
