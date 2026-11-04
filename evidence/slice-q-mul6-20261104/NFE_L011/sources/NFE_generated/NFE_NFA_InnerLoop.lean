import NFE_NFA_InnerStep
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFE_NFA_InnerLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1
/-- Induction over the actual extracted inner loop, preserving rejection and
using no independently successful child premise. -/
theorem accepted (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (canonical : NEV_DotInputs.Canonical g) (slot : Usize) (fuel : Nat)
    (iter : core.ops.range.Range Usize) (sums : Array U64 8#usize)
    (n : Nat) (width : n+fuel≤4) (span : iter.start.val+fuel=iter.end.val)
    (endpoint : iter.end.val≤26) (invariant : NFE_NEV_DotSweep.Sweep n 0 sums)
    (out : Array U64 8#usize)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0 iter q g slot sums=ok out) :
    NFE_NEV_DotSweep.Sweep (n+fuel) 0 out := by
  induction fuel generalizing iter sums n with
  | zero =>
    have halt : iter.end.val ≤ iter.start.val := by omega
    obtain ⟨⟨o,cursor⟩,advance,value,rest⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_none_spec
        (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
        (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x y;rfl) iter halt)
    subst o
    have body : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot iter sums=ok (done sums) := by
      rw [NEV_ActualDotStep.body]
      simp only [NEV_ActualDotStep.step,advance,bind_tc_ok]
      rfl
    unfold FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0 at run
    rw [Aeneas.Std.loop.eq_def] at run
    dsimp only at run
    simp only [body,bind_tc_ok] at run
    have same : sums=out:=Result.ok.inj run
    simpa only [Nat.add_zero,same] using invariant
  | succ k ih =>
    have inside : iter.start.val < iter.end.val := by omega
    unfold FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0 at run
    rw [Aeneas.Std.loop.eq_def] at run
    dsimp only at run
    cases bodyRun : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot iter sums with
    | fail error => simp only [bodyRun,bind_tc_fail] at run;cases run
    | div => simp only [bodyRun,bind_tc_div] at run;cases run
    | ok flow =>
      obtain ⟨next,after,tag⟩:=NFE_NFA_InnerStep.shape q g slot iter sums inside flow bodyRun
      subst flow
      obtain ⟨counter,finish,bound⟩:=NFE_NFA_InnerStep.accepted q g canonical slot iter sums n
        (by omega) inside endpoint invariant next after bodyRun
      simp only [bodyRun,bind_tc_ok] at run
      have result:=ih next after (n+1) (by omega) (by rw [finish];omega)
        (by rw [finish];exact endpoint) bound run
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
#print axioms accepted
end NFE_NFA_InnerLoop
end
