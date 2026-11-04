import NFA_OuterStep
import Port3_PushFrame
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AspisR1.NFA_OuterAccepted
open Aeneas Aeneas.Std Result ControlFlow
/-- An active successful actual outer step preserves the SAME complete array
bound. The inner result is read from that run; no independent success is assumed. -/
theorem step (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients) (slot : Usize)
    (iter : NFA_Iterator.Iter) (limbs : Array U64 8#usize) (n : Nat) (active : n<7)
    (stride : iter.step_by.val=4) (finish : iter.iter.end.val=26)
    (inside : iter.iter.start.val < iter.iter.end.val) (bound : NFA_FoldEight.Bound limbs n)
    (flow : ControlFlow (NFA_Iterator.Iter × Array U64 8#usize) (Array U64 8#usize))
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0.body q g slot iter limbs=ok flow) :
    ∃ next out,flow=cont (next,out) ∧
      next.iter.start.val=min (iter.iter.start.val+4) 26 ∧ next.iter.end.val=26 ∧
      next.step_by.val=4 ∧ NFA_FoldEight.Bound out (n+1) := by
  obtain ⟨cursor,advance,start,endpoint,stride'⟩:=NFA_Iterator.next iter stride inside
  rw [NFA_OuterStep.body] at run
  simp only [NFA_OuterStep.step,advance,bind_tc_ok,Aeneas.Std.uncurry] at run
  obtain ⟨end4,add,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨stop,minimum,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨sums,inner,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨out,fold,tag⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨actual,actualRun,post⟩:=NFA_FoldEight.source sums limbs n active bound
  have same : actual=out:=Result.ok.inj (actualRun.symm.trans fold)
  exact ⟨cursor,out,(Result.ok.inj tag).symm,by simpa only [finish] using start,
    by simpa only [endpoint] using finish,stride',same ▸ post⟩
/-- Every scalar fold native window gets its numeric caller domain from the
actual reached array, with unused cells unrestricted. -/
theorem native_domain (limbs : Array U64 8#usize) (n : Nat) (active : n<7)
    (bound : NFA_FoldEight.Bound limbs n) (index : Usize) (inside : index.val<8)
    (word : U64) (run : Array.index_usize limbs index=ok word) : word.val<137438953472 := by
  obtain ⟨actual,actualRun,point⟩:=WP.spec_imp_exists
    (Array.index_usize_spec limbs index (by change index.val<limbs.val.length;rw [limbs.property];exact inside))
  have same : actual=word:=Result.ok.inj (actualRun.symm.trans run)
  have member : word∈limbs.val := by rw [← same,point];exact List.getElem_mem _
  have b:=bound word member
  have cap:=Nat.mul_le_mul_right NFA_FoldLane.R (show n≤6 by omega)
  norm_num [NFA_FoldLane.R] at b cap
  omega
#print axioms step
#print axioms native_domain
end AspisR1.NFA_OuterAccepted
end
