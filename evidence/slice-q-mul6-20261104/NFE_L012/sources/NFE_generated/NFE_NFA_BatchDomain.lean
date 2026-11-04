import NFE_NFA_InnerLoop
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AspisR1.NFE_NFA_BatchDomain
open Aeneas Aeneas.Std Result
/-- Generic exact min operation; no fixture-specific inputs or oracle. -/
theorem minimum (a b : Usize) :
    ∃ c,core.cmp.min core.cmp.OrdUsize a b=ok c ∧ c.val=min a.val b.val := by
  have spec : core.cmp.min core.cmp.OrdUsize a b ⦃ c=>c.val=min a.val b.val ⦄ := by
    unfold core.cmp.min
    step*
    all_goals scalar_tac
  exact WP.spec_imp_exists spec
/-- The actual checked batch endpoint establishes the complete inner domain. -/
theorem endpoint (start : Usize) (active : start.val<26) :
    ∃ end4 stop,start+4#usize=ok end4 ∧ core.cmp.min core.cmp.OrdUsize end4 26#usize=ok stop ∧
      start.val≤stop.val ∧ stop.val≤26 ∧ stop.val-start.val≤4 ∧ stop.val=min (start.val+4) 26 := by
  obtain ⟨end4,add,value⟩:=WP.spec_imp_exists
    (UScalar.add_spec (x:=start) (y:=4#usize) (by scalar_tac))
  obtain ⟨stop,run,meaning⟩:=minimum end4 26#usize
  have same : stop.val=min (start.val+4) 26 := by
    simpa only [value,show (4#usize).val=4 from rfl,show (26#usize).val=26 from rfl] using meaning
  exact ⟨end4,stop,add,run,by omega,by omega,by omega,same⟩
/-- Every successful SAME inner invocation from zero has the four-product
bound; the endpoint facts are precisely those derived above. -/
theorem returned (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (canonical : NEV_DotInputs.Canonical g) (slot start stop : Usize)
    (ordered : start.val≤stop.val) (finish : stop.val≤26) (width : stop.val-start.val≤4)
    (out : Array U64 8#usize)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0 {start,«end»:=stop} q g slot
      (Array.repeat 8#usize 0#u64)=ok out) :
    NFE_NEV_DotSweep.Sweep (stop.val-start.val) 0 out := by
  have h:=NFE_NFA_InnerLoop.accepted q g canonical slot (stop.val-start.val) {start,«end»:=stop}
    (Array.repeat 8#usize 0#u64) 0 (by omega) (by dsimp only;omega) finish
    NFE_NEV_DotEightTotal.zero out run
  simpa only [Nat.zero_add] using h
#print axioms minimum
#print axioms endpoint
#print axioms returned
end AspisR1.NFE_NFA_BatchDomain
end
