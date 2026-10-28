import R1Z.PV_RDB2C_PV_B2_C_PowersBody
set_option autoImplicit false
namespace PV_B2_C_PowersTotal
open Aeneas Aeneas.Std Result ControlFlow PV_B2_251c1 PV_B2_C_PowersBody

theorem done {N : Usize} (x : E) (out : Array E N) (p : E) (i : Usize)
    (hi : ¬ i < N) : prover_powers.powers_loop x out p i = ok out := by
  unfold prover_powers.powers_loop
  rw [Aeneas.Std.loop.eq_def]
  simp only [prover_powers.powers_loop.body,hi,if_false]

theorem step {N : Usize} (x : E) (out updated : Array E N) (p p1 : E)
    (i : Usize) (hb : prover_powers.powers_loop.body x out p i =
      ok (cont (updated,p1,Usize.wrapping_add i 1#usize))) :
    prover_powers.powers_loop x out p i =
      prover_powers.powers_loop x updated p1 (Usize.wrapping_add i 1#usize) := by
  unfold prover_powers.powers_loop
  rw [Aeneas.Std.loop.eq_def]
  simp only [hb]

theorem loop_total {N : Usize} (x : E) (out : Array E N) (p : E) (i : Usize) :
    ∃ updated, prover_powers.powers_loop x out p i = ok updated := by
  suffices ∀ n (i : Usize) (out : Array E N) (p : E), N.val-i.val = n →
      ∃ updated, prover_powers.powers_loop x out p i = ok updated from
    this (N.val-i.val) i out p rfl
  intro n
  induction n with
  | zero =>
    intro i out p hn
    have hi : ¬ i < N := by scalar_tac
    exact ⟨out,done x out p i hi⟩
  | succ n ih =>
    intro i out p hn
    have hi : i < N := by scalar_tac
    obtain ⟨out1,p1,hb⟩ := body_total x out p i hi
    have hn1 : N.val-(Usize.wrapping_add i 1#usize).val = n := by
      rw [next_val i hi]
      omega
    obtain ⟨out2,ho⟩ := ih (Usize.wrapping_add i 1#usize) out1 p1 hn1
    exact ⟨out2,(step x out out1 p p1 i hb).trans ho⟩

theorem source (N : Usize) (x : E) : ∃ out, prover_powers.powers N x = ok out := by
  exact loop_total x _ _ _
#print axioms done
#print axioms step
#print axioms loop_total
#print axioms source
end PV_B2_C_PowersTotal
