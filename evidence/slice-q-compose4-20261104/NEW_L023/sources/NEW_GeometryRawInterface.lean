import NEW_GeometryPrefix
import NEB_ActualGeometryModel
set_option autoImplicit false
namespace NEW_GeometryRawInterface
open Aeneas Aeneas.Std Result AspisR1
namespace N
abbrev G := NEW_GeometryActual.verifier.QueryGeometry
abbrev E := NEW_GeometryActual.verifier.Error
end N
namespace O
abbrev G := AspisR1Stage2.verifier.QueryGeometry
abbrev E := AspisR1Stage2.verifier.Error
end O

def geometry (g : N.G) : O.G := ⟨g.start,g.inverses,g.line_z⟩
def geometryBack (g : O.G) : N.G := ⟨g.start,g.inverses,g.line_z⟩
def error : N.E → O.E
 | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
 | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
 | .Checkpoint => .Checkpoint | .Allocation => .Allocation

def errorBack : O.E → N.E
 | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
 | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
 | .Checkpoint => .Checkpoint | .Allocation => .Allocation

def answer : core.result.Result N.G N.E → core.result.Result O.G O.E
 | .Ok g => .Ok (geometry g)
 | .Err e => .Err (error e)

def answerBack : core.result.Result O.G O.E → core.result.Result N.G N.E
 | .Ok g => .Ok (geometryBack g)
 | .Err e => .Err (errorBack e)

theorem geometry_roundtrip (g : N.G) : geometryBack (geometry g)=g := by cases g; rfl
theorem geometry_reverse (g : O.G) : geometry (geometryBack g)=g := by cases g; rfl
theorem error_roundtrip (e : N.E) : errorBack (error e)=e := by cases e <;> rfl
theorem error_reverse (e : O.E) : error (errorBack e)=e := by cases e <;> rfl
theorem answer_roundtrip (r : core.result.Result N.G N.E) : answerBack (answer r)=r := by
 cases r with
 | Ok g => cases g; rfl
 | Err e => cases e <;> rfl

theorem answer_reverse (r : core.result.Result O.G O.E) : answer (answerBack r)=r := by
 cases r with
 | Ok g => cases g; rfl
 | Err e => cases e <;> rfl

/-- Complete dictionary read directly from the actual extracted caller.
No result equality, parent acceptance or freely chosen child operation. -/
def ops : Port3_NativeGeometryBody.Ops NEW_GeometryActual.aspis_core.r0.Error where
 op0 := core.array.from_fn
 op1 := core.iter.traits.iterator.Iterator.map.default
 op2 := core.result.Result.map_err
 op3 := core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
 op4 := alloc.vec.Vec.is_empty
 op5 := NEW_GeometryActual.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
 op6 := ok NEW_GeometryActual.aspis_core.field.M31.ZERO
 op7 := ok NEW_GeometryActual.aspis_core.field.M31.ONE
 op8 := NEW_GeometryActual.aspis_core.field.M31.sub
 op9 := NEW_GeometryActual.aspis_core.field.M31.mul
 op10 := NEW_GeometryActual.aspis_core.field.M31.double
 op11 := NEW_GeometryActual.aspis_core.field.M31.inv
 op12 := NEW_GeometryActual.aspis_core.r0.domain.FibreIndex.new
 op13 := NEW_GeometryActual.verifier.batch_prefix_products
 op14 := NEW_GeometryActual.fast_domain.line_node
 op15 := fun u => do
   let p ← NEW_GeometryActual.fast_domain.fibre_point u
   ok ⟨p.x,p.y⟩
 mapIterator := fun it f => ⟨core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next it f⟩

#print axioms geometry_roundtrip
#print axioms geometry_reverse
#print axioms error_roundtrip
#print axioms error_reverse
#print axioms answer_roundtrip
#print axioms answer_reverse
#print axioms ops
end NEW_GeometryRawInterface
