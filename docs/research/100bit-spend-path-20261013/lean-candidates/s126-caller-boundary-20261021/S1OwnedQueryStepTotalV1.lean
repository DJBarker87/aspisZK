import S1OwnedQueryContainsTotalV1
set_option autoImplicit false
namespace AspisS1OwnedQueryBlock.Total
open Aeneas Aeneas.Std Result ControlFlow

private theorem mk (n : Nat) (h : UScalar.inBounds .Usize n) :
    UScalar.tryMk .Usize n=ok (Usize.ofNatCore n h) := by
  simp only [UScalar.tryMk,UScalar.tryMkOpt,
    dif_pos ((UScalar.check_bounds_eq_inBounds .Usize n).mpr h),Result.ofOption]
  rfl

/-- TOTAL one-word transition, including the stopped states. No membership,
canonicality, distinctness, or child-success premise is required. -/
theorem step_total (a : Array U32 22#usize) (len draws : Usize) (candidate : U32)
    (hlen : len.val≤22) (hdraws : draws.val≤64) :
    ∃ (a' : Array U32 22#usize) (len' draws' : Usize) (stop : Bool),
      owned_step a len draws candidate=ok (a',len',draws',stop) ∧
      len'.val≤22 ∧ draws'.val≤64 := by
  by_cases full : len=22#usize
  · exact ⟨a,len,draws,true,by simp only [owned_step,if_pos full],hlen,hdraws⟩
  by_cases exhausted : draws=64#usize
  · exact ⟨a,len,draws,true,by simp only [owned_step,if_neg full,if_pos exhausted],hlen,hdraws⟩
  have lenBound : len.val<22 := by scalar_tac
  have drawBound : draws.val<64 := by scalar_tac
  let d : Usize := Usize.ofNatCore (draws.val+1) (by scalar_tac)
  have dval : d.val=draws.val+1 := by simp [d]
  have addDraw : draws+1#usize=ok d := by
    change UScalar.tryMk .Usize (draws.val+1)=_
    exact mk _ _
  obtain ⟨found,call⟩ := contains_total a len candidate hlen
  cases found with
  | true =>
    refine ⟨a,len,d,false,?_,hlen,by omega⟩
    simp only [owned_step,if_neg full,if_neg exhausted,addDraw,call,bind_tc_ok]
    rfl
  | false =>
    let n : Usize := Usize.ofNatCore (len.val+1) (by scalar_tac)
    have nval : n.val=len.val+1 := by simp [n]
    have addLen : len+1#usize=ok n := by
      change UScalar.tryMk .Usize (len.val+1)=_
      exact mk _ _
    have updated := AspisS1QueryArrayOperations.update_total a len candidate (by scalar_tac)
    refine ⟨a.set len candidate,n,d,false,?_,by omega,by omega⟩
    simp only [owned_step,if_neg full,if_neg exhausted,addDraw,call,updated,addLen,bind_tc_ok]
    rfl

#print axioms step_total
end AspisS1OwnedQueryBlock.Total
