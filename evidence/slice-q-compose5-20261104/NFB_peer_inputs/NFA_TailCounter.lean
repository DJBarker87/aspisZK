import NFA_TailQM
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFA_TailCounter
open Aeneas Aeneas.Std Result
/-- Successful actual push advances the SAME receiver count. Child arithmetic
is retained as its actual monadic computation, never replaced by assumed success. -/
theorem step (self : FIo_Native.fast_pairing.EbyKDot) (value : NEV_DotCarrier.NE)
    (scalar : NEV_DotCarrier.NQ) (after : FIo_Native.fast_pairing.EbyKDot)
    (small : self.count.val<3)
    (run : FIo_Native.fast_pairing.EbyKDot.push self value scalar=ok (.Ok (),after)) :
    after.count.val=self.count.val+1 := by
  have below : ¬self.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    simp only [FIo_Native.fast_pairing.MAX_TERMS]
    scalar_tac
  unfold FIo_Native.fast_pairing.EbyKDot.push at run
  rw [if_neg below] at run
  iterate 3 obtain ⟨x,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨checked,check,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  cases checked with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at run
    cases run
  | Ok q =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
    obtain ⟨left,callLeft,run⟩:=Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨right,callRight,run⟩:=Port3_PushFrame.bind_success _ _ _ run
    simp only [lift,bind_tc_ok] at run
    have same : Usize.wrapping_add self.count 1#usize=after.count :=
      congrArg (fun p=>p.2.count) (Result.ok.inj run)
    rw [← same,Usize.wrapping_add_val_eq]
    change (self.count.val+1)%UScalar.size .Usize=self.count.val+1
    apply Nat.mod_eq_of_lt
    have limit:=(4096#usize).hSize
    change 4096<UScalar.size .Usize at limit
    omega
/-- Both input native window guards follow from source-reachable tail positions. -/
theorem windows (slot position : Nat) (slotBound : slot<4) (positionBound : position<3) :
    (if position=0 then slot*120+104 else 480+slot*32+(position-1)*16)+16≤608 ∧
    (if position=0 then 28 else 25+position)<29 ∧ position<4096 := by
  split_ifs <;> omega
#print axioms step
#print axioms windows
end AspisR1.NFA_TailCounter
end
