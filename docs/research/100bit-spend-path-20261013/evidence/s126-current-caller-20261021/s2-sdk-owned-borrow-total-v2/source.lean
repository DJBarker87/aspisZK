import S2SdkOwnedPrimitivesTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS2OwnedStage1.SdkReference.BorrowTotal

/-- The actual shared-borrow guard implies signed checked increment cannot
fail or return None, including the isize::MAX-1 boundary. -/
theorem shared_increment_total (counter : Isize)
    (allowed : shared_allowed counter=ok true) :
    ∃ next : Isize, (counter+1#isize : Result Isize)=ok next ∧
      Isize.checked_add counter 1#isize=some next ∧ next.val=counter.val+1 := by
  have bounds := (PrimitivesTotal.shared_allowed_true counter).mp allowed
  have hs : (counter+1#isize : Result Isize) ⦃ next => next.val=counter.val+(1#isize).val ⦄ := by
    apply IScalar.add_spec <;> scalar_tac
  obtain ⟨next,hnext,hvalue⟩ := spec_imp_exists hs
  refine ⟨next,hnext,?_,by simpa using hvalue⟩
  unfold Isize.checked_add core.num.checked_add_IScalar
  rw [hnext]
  rfl

#print axioms shared_increment_total
end AspisS2OwnedStage1.SdkReference.BorrowTotal
