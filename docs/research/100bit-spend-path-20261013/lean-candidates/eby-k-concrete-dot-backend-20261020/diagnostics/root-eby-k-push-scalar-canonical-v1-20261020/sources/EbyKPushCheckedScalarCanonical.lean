import EbyKCheckedQCanonicality
import AspisR1EbyKPushConcreteCheckedQV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1EbyKPushCheckedScalarCanonical
open AspisR1EbyKPushExplicitOpsV1 AspisR1EbyKPushSourceConversionV1
open AspisR1EbyKPushConcreteCheckedQV1

theorem successful_push_scalar_canonical
    (pushDot : Dot → Q → Q → Result Dot)
    (self : State) (value : Wide) (scalar : Qm) (out : State)
    (hrun : pushWithConcreteCheckedQ AspisR1EbyKCheckedQConcreteAll.concreteAll
      pushDot self value scalar = .ok (.Ok (),out)) :
    ∀ x ∈ [scalar.c0.a,scalar.c0.b,scalar.c1.a,scalar.c1.b],
      x.val < 2147483647 := by
  have hshape := push_source_conversion_success_shape
    (AspisR1EbyKCheckedQAllParamV1.checkedQWithAll AspisR1EbyKCheckedQConcreteAll.concreteAll)
    pushDot UScalar.add self value scalar out (by
      simpa only [pushWithConcreteCheckedQ,pushWithSourceCheckedAdd,pushWithSourceConversion] using hrun)
  rcases hshape with ⟨arr,x0,x1,r,val,d0,d1,i,harr,hcoords,hx0,hx1,hr,hbranch,hd0,hd1,hinc,hout⟩
  cases r with
  | Ok q =>
    have hq := AspisR1EbyKCheckedQConcreteAll.checkedQ_success_canonical scalar q hr
    rw [hq.1] at hq
    exact hq.2
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch] at hbranch
    cases hbranch

#print axioms successful_push_scalar_canonical
end AspisR1EbyKPushCheckedScalarCanonical
