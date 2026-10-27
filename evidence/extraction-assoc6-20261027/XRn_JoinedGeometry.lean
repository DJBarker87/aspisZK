import XRn_Join_Funs
import Port3_NativeGeometryBody
import Port5Q1_GeometryAccessor
import ExtractedCurrentReducerOps
open Aeneas Aeneas.Std Result
open XRn_Join_Release
set_option autoImplicit false
namespace XRn_JoinedGeometry
def inner {A B F G : Type} (f : A → B) (g : F → G) : core.result.Result A F → core.result.Result B G
 | .Ok a => .Ok (f a) | .Err e => .Err (g e)
def mapR {A B : Type} (f : A → B) (r : Result A) : Result B := do
 let a ← r
 ok (f a)

/-- Current stage2 cohort geometry has the SAME cache field. The retired
cache-free model still needs its separate recomputation transport. -/
def cohort (g : verifier.QueryGeometry) : AspisR1Stage2.verifier.QueryGeometry :=
 ⟨g.start,g.inverses,g.line_z⟩
def emitted (g : AspisR1Stage2.verifier.QueryGeometry) : verifier.QueryGeometry :=
 ⟨g.start,g.inverses,g.line_z⟩
def error : verifier.Error → AspisR1Stage2.verifier.Error
 | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
 | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
 | .Checkpoint => .Checkpoint | .Allocation => .Allocation

theorem cohort_emitted (g : AspisR1Stage2.verifier.QueryGeometry) : cohort (emitted g)=g := by cases g; rfl
theorem emitted_cohort (g : verifier.QueryGeometry) : emitted (cohort g)=g := by cases g; rfl

/-- Full Result, including checked-index subtraction failure and indexing
failure. No successful query is assumed. -/
theorem for_query (g : verifier.QueryGeometry) (i : Usize) (order : g.start.val ≤ i.val) :
 verifier.QueryGeometry.for_query g i=AspisR1.Port5Q1_GeometryBinding.forQuery (cohort g) i := by
 obtain ⟨offset,checked,value⟩ := AspisR1.ExtractedCurrentReducerOps.sub_success i g.start order
 have wrapped := AspisR1.Port5Q1_GeometryAccessor.offset i g.start order
 have same : offset=Usize.wrapping_sub i g.start := UScalar.eq_of_val_eq (value.trans wrapped.symm)
 unfold verifier.QueryGeometry.for_query AspisR1.Port5Q1_GeometryBinding.forQuery
 change (i-g.start : Result Usize)=ok offset at checked
 simp only [checked,bind_tc_ok,same,cohort]

theorem reversed_range {CoreError : Type} (ops : AspisR1.Port3_NativeGeometryBody.Ops CoreError)
 (queries : Array U32 22#usize) (start finish : Usize) (bad : start>finish) :
 mapR (inner cohort error) (verifier.QueryGeometry.for_range queries start finish)=
 AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range ops queries start finish := by
 unfold verifier.QueryGeometry.for_range AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range
 simp only [bad,if_pos,mapR,bind_tc_ok,inner,error]

#print axioms cohort_emitted
#print axioms emitted_cohort
#print axioms for_query
#print axioms reversed_range
end XRn_JoinedGeometry
