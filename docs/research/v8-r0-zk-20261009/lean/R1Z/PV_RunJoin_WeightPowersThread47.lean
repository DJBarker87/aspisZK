import R1Z.PV_RunJoin_WeightBorrow46
import R1Z.PV_RunJoin_WeightWide46
import R1Z.PV_B2_C_Powers7Total
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPowersThread47
open Aeneas Aeneas.Std Result PV_B2_251c1
open PV_RunJoin_WeightWide46 (E)

theorem read {N : Usize} (out : Array E N) (i : Usize) (hi : i<N) :
    ∃ old, Array.index_usize out i=ok old := by
  obtain ⟨old,hr,_⟩ := WP.spec_imp_exists (Array.index_usize_spec out i (by
    change i.val<out.val.length
    rw [out.property]
    scalar_tac))
  exact ⟨old,hr⟩
#print axioms read

theorem more {N : Usize} (x p : E) (out : Array E N) (i : Usize)
    (hi : i<N) (hm : Usize.wrapping_add i 1#usize<N) :
    prover_powers.powers_loop x out p i=
      prover_powers.powers_loop x (Aeneas.Std.Array.set out i p)
        (PV_B2_C_251WideValue.aspis_core.field.wide_exact.WideExact.mul p x)
        (Usize.wrapping_add i 1#usize) := by
  obtain ⟨old,hr⟩ := read out i hi
  apply PV_B2_C_PowersTotal.step
  simp only [prover_powers.powers_loop.body,if_pos hi,Array.index_mut_usize,
    hr,bind_tc_ok,lift,if_pos hm,PV_B2_C_251WideTotal.WideExact_mul]
  rfl
#print axioms more

theorem last {N : Usize} (x p : E) (out : Array E N) (i : Usize)
    (hi : i<N) (hm : ¬ Usize.wrapping_add i 1#usize<N) :
    prover_powers.powers_loop x out p i=ok (Aeneas.Std.Array.set out i p) := by
  obtain ⟨old,hr⟩ := read out i hi
  have hb : prover_powers.powers_loop.body x out p i=
      ok (.cont (Aeneas.Std.Array.set out i p,p,Usize.wrapping_add i 1#usize)) := by
    simp only [prover_powers.powers_loop.body,if_pos hi,Array.index_mut_usize,
      hr,bind_tc_ok,lift,if_neg hm]
    rfl
  rw [PV_B2_C_PowersTotal.step x out _ p p i hb]
  exact PV_B2_C_PowersTotal.done x _ p _ hm
#print axioms last
end R1Z.PV_RunJoin_WeightPowersThread47
