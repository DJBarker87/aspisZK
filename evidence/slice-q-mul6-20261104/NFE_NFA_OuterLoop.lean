import NFE_NFA_OuterAccepted
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AspisR1.NFE_NFA_OuterLoop
open Aeneas Aeneas.Std Result ControlFlow
/-- Seven-batch induction over the actual adopted loop, on arbitrary bytes and
coefficients. Invalid scalar reads retain the actual rejecting Result branch. -/
theorem accepted (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients) (slot : Usize)
    (fuel : Nat) (iter : NFA_Iterator.Iter) (limbs : Array U64 8#usize)
    (n : Nat) (remaining : n+fuel=7) (stride : iter.step_by.val=4)
    (finish : iter.iter.end.val=26) (cursor : iter.iter.start.val=min (4*n) 26)
    (bound : NFE_NFA_FoldEight.Bound limbs n) (out : Array U64 8#usize)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0 iter q g slot limbs=ok out) :
    NFE_NFA_FoldEight.Bound out 7 := by
  induction fuel generalizing iter limbs n with
  | zero =>
    have sameN : n=7 := by omega
    have halt : iter.iter.end.val ≤ iter.iter.start.val := by omega
    have body : FIp_NativeDots.fast_dots.four_dots_one_loop0.body q g slot iter limbs=ok (done limbs) := by
      rw [NFE_NFA_OuterStep.body]
      simp only [NFE_NFA_OuterStep.step,NFA_Iterator.stopped iter halt,bind_tc_ok,Aeneas.Std.uncurry]
    unfold FIp_NativeDots.fast_dots.four_dots_one_loop0 at run
    rw [Aeneas.Std.loop.eq_def] at run
    dsimp only at run
    simp only [body] at run
    have same : limbs=out:=Result.ok.inj run
    simpa only [same,sameN] using bound
  | succ k ih =>
    have active : n<7 := by omega
    have inside : iter.iter.start.val < iter.iter.end.val := by omega
    unfold FIp_NativeDots.fast_dots.four_dots_one_loop0 at run
    rw [Aeneas.Std.loop.eq_def] at run
    dsimp only at run
    cases bodyRun : FIp_NativeDots.fast_dots.four_dots_one_loop0.body q g slot iter limbs with
    | fail error => simp only [bodyRun] at run;cases run
    | div => simp only [bodyRun] at run;cases run
    | ok flow =>
      obtain ⟨next,after,tag,start,end',stride',post⟩:=NFE_NFA_OuterAccepted.step q g slot iter limbs n
        active stride finish inside bound flow bodyRun
      subst flow
      simp only [bodyRun] at run
      apply ih next after (n+1) (by omega) stride' end' ?_ post run
      rw [start,cursor]
      omega
/-- The literal initialized entry supplies the invariant without an extra
successful child, arbitrary array snapshot or byte-canonicality hypothesis. -/
theorem initialized (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients) (slot : Usize)
    (out : Array U64 8#usize)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0 (NFA_Iterator.value 0) q g slot
      (Array.repeat 8#usize 0#u64)=ok out) : NFE_NFA_FoldEight.Bound out 7 := by
  apply accepted q g slot 7 (NFA_Iterator.value 0) (Array.repeat 8#usize 0#u64) 0
    (by omega) rfl rfl rfl ?_ out run
  intro x hx
  change x∈List.replicate 8 (0#u64) at hx
  have same : x=0#u64 := (List.mem_replicate.mp hx).2
  subst x
  simp
#print axioms accepted
#print axioms initialized
end AspisR1.NFE_NFA_OuterLoop
end
