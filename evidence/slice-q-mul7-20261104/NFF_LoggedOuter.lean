import NFF_LoggedOuterStep
import NFE_NFA_OuterLoop
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AspisR1.NFF_LoggedOuter
open Aeneas Aeneas.Std Result ControlFlow

def run (oracle : NFF_LoggedEight.Oracle) (q : Array U8 608#usize)
    (g : NEV_DotInputs.Coefficients) (slot : Usize) : Nat →
    NFA_Iterator.Iter → Array U64 8#usize → Result (Array U64 8#usize)
  | 0,_,limbs => ok limbs
  | fuel+1,iter,limbs => do
    let flow ← NFF_LoggedOuterStep.step oracle q g slot iter limbs
    match flow with
    | done out => ok out
    | cont (next,out) => run oracle q g slot fuel next out

theorem replay (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (domain : NEV_DotInputs.Canonical g) (slot : Usize) (fuel : Nat)
    (iter : NFA_Iterator.Iter) (limbs : Array U64 8#usize)
    (n : Nat) (remaining : n+fuel=7) (stride : iter.step_by.val=4)
    (finish : iter.iter.end.val=26) (cursor : iter.iter.start.val=min (4*n) 26)
    (bound : NFE_NFA_FoldEight.Bound limbs n) :
    run oracle q g slot fuel iter limbs=
      FIp_NativeDots.fast_dots.four_dots_one_loop0 iter q g slot limbs := by
  induction fuel generalizing iter limbs n with
  | zero =>
    have halt : iter.iter.end.val ≤ iter.iter.start.val := by omega
    have body:= (NFF_LoggedOuterStep.stopped oracle q g slot iter limbs halt).2
    unfold FIp_NativeDots.fast_dots.four_dots_one_loop0
    rw [Aeneas.Std.loop.eq_def]
    dsimp only
    simp only [run,body,bind_tc_ok]
  | succ k ih =>
    have active : n<7 := by omega
    have inside : iter.iter.start.val < iter.iter.end.val := by omega
    have stepEq:=NFF_LoggedOuterStep.active oracle law q g domain slot iter limbs stride finish inside
    simp only [run,stepEq]
    unfold FIp_NativeDots.fast_dots.four_dots_one_loop0
    rw [Aeneas.Std.loop.eq_def]
    dsimp only
    cases bodyRun : FIp_NativeDots.fast_dots.four_dots_one_loop0.body q g slot iter limbs with
    | fail e => simp only [bodyRun,bind_tc_fail]
    | div => simp only [bodyRun,bind_tc_div]
    | ok flow =>
      obtain ⟨next,after,tag,start,end',stride',post⟩:=NFE_NFA_OuterAccepted.step q g slot iter limbs n
        active stride finish inside bound flow bodyRun
      subst flow
      simp only [bodyRun,bind_tc_ok]
      apply ih next after (n+1) (by omega) stride' end' ?_ post
      rw [start,cursor]
      omega

theorem initialized (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (domain : NEV_DotInputs.Canonical g) (slot : Usize) :
    run oracle q g slot 7 (NFA_Iterator.value 0) (Array.repeat 8#usize 0#u64)=
      FIp_NativeDots.fast_dots.four_dots_one_loop0 (NFA_Iterator.value 0) q g slot
        (Array.repeat 8#usize 0#u64) := by
  apply replay oracle law q g domain slot 7 (NFA_Iterator.value 0)
    (Array.repeat 8#usize 0#u64) 0 (by omega) rfl rfl rfl
  intro x hx
  change x∈List.replicate 8 (0#u64) at hx
  have same : x=0#u64 := (List.mem_replicate.mp hx).2
  subst x
  simp

#print axioms replay
#print axioms initialized
end AspisR1.NFF_LoggedOuter
end
