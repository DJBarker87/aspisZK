import NFF_LoggedStep
import NFE_NFA_InnerLoop
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AspisR1.NFF_LoggedLoop
open Aeneas Aeneas.Std Result ControlFlow

def run (oracle : NFF_LoggedEight.Oracle) (q : Array U8 608#usize)
    (g : NEV_DotInputs.Coefficients) (slot : Usize) : Nat →
    core.ops.range.Range Usize → Array U64 8#usize → Result (Array U64 8#usize)
  | 0,_,sums => ok sums
  | fuel+1,iter,sums => do
    let flow ← NFF_LoggedStep.step oracle q g slot iter sums
    match flow with
    | done out => ok out
    | cont (next,out) => run oracle q g slot fuel next out

/-- Native arbitrary-prestate one-step transport composes by induction over
the actual loop's range. No whole-buffer Kani claim or independent successful
iteration is a premise, and failed parses keep their exact Result. -/
theorem replay (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (domain : NEV_DotInputs.Canonical g) (slot : Usize) (fuel : Nat)
    (iter : core.ops.range.Range Usize) (sums : Array U64 8#usize)
    (n : Nat) (width : n+fuel≤4) (span : iter.start.val+fuel=iter.end.val)
    (endpoint : iter.end.val≤26) (invariant : NFE_NEV_DotSweep.Sweep n 0 sums) :
    run oracle q g slot fuel iter sums=
      FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0 iter q g slot sums := by
  induction fuel generalizing iter sums n with
  | zero =>
    have halt : iter.end.val ≤ iter.start.val := by omega
    obtain ⟨⟨o,cursor⟩,advance,value,rest⟩:=WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_none_spec
        (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
        (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x y;rfl) iter halt)
    subst o
    have body : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot iter sums=ok (done sums) := by
      rw [NEV_ActualDotStep.body]
      simp only [NEV_ActualDotStep.step,advance,bind_tc_ok]
      rfl
    unfold FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0
    rw [Aeneas.Std.loop.eq_def]
    dsimp only
    simp only [run,body,bind_tc_ok]
  | succ k ih =>
    have inside : iter.start.val < iter.end.val := by omega
    have stepEq:=NFF_LoggedStep.active oracle law q g domain slot iter sums inside endpoint
    simp only [run,stepEq]
    unfold FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0
    rw [Aeneas.Std.loop.eq_def]
    dsimp only
    cases bodyRun : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot iter sums with
    | fail e => simp only [bodyRun,bind_tc_fail]
    | div => simp only [bodyRun,bind_tc_div]
    | ok flow =>
      obtain ⟨next,after,tag⟩:=NFE_NFA_InnerStep.shape q g slot iter sums inside flow bodyRun
      subst flow
      obtain ⟨counter,finish,bound⟩:=NFE_NFA_InnerStep.accepted q g domain slot iter sums n
        (by omega) inside endpoint invariant next after bodyRun
      simp only [bodyRun,bind_tc_ok]
      exact ih next after (n+1) (by omega) (by rw [finish];omega)
        (by rw [finish];exact endpoint) bound

#print axioms replay
end AspisR1.NFF_LoggedLoop
end
