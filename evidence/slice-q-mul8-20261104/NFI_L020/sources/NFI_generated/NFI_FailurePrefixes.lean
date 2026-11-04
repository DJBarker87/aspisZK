import NFI_InnerTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFI_FailurePrefixes
open Aeneas Aeneas.Std Result

/-- Rejection at the reached scalar read occurs before coefficient access or
any product update; no canonical-g premise is needed on this prefix. -/
theorem rejected (oracle : NFF_LoggedEight.Oracle) (q : Array U8 608#usize)
    (g : NEV_DotInputs.Coefficients) (slot : Usize)
    (iter : core.ops.range.Range Usize) (sums : Array U64 8#usize)
    (active : iter.start.val<iter.end.val) (e : Error)
    (read : NEV_DotRead.read q slot iter.start=fail e) :
    NFF_LoggedStep.step oracle q g slot iter sums=fail e := by
  obtain ⟨⟨o,cursor⟩,advance,value,start,finish⟩:=WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl)
      iter active)
  subst o
  simp only [NFF_LoggedStep.step,advance,bind_tc_ok,Aeneas.Std.uncurry,read,bind_tc_fail]

theorem trace_prefix (oracle : NFF_LoggedEight.Oracle) (fuel : Nat)
    (before : NFI_InnerCut.Cut) (active : before.iter.start.val<before.iter.end.val)
    (e : Error) (read : NEV_DotRead.read before.input.q before.input.slot before.iter.start=fail e) :
    (NFI_InnerTrace.run oracle (fuel+1) before).1=fail e ∧
    (NFI_InnerTrace.run oracle (fuel+1) before).2=[before] := by
  have h : NFI_InnerCut.step oracle before=fail e := by
    simp only [NFI_InnerCut.step,rejected oracle before.input.q before.input.g
      before.input.slot before.iter before.sums active e read,bind_tc_fail]
  simp [NFI_InnerTrace.run,h]

#print axioms rejected
#print axioms trace_prefix
end AspisR1.NFI_FailurePrefixes
end
