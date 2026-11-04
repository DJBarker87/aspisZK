import Lean
import NFN_PhaseTransport
import NFN_ReserveOwner
import NFN_GeometryPart03
import Port4C_NativePrefix
import Port5Q1_Geometry
import NEW_LoopMap
import NEW_ResultMapSyntax
import NEW_LiteralRefl
import NEW_ShiftAssociation

-- BEGIN copied NEW_GeometryPrefix: evidence/slice-q-compose4-20261104/NEW_GeometryPrefix.lean
set_option autoImplicit false
namespace NFN_NEW_GeometryPrefix
open Aeneas Aeneas.Std Result AspisR1

def leaves : Port4C_NativePrefix.Leaves := ⟨AspisR1Qm31ArithmeticProbe.field.M31.mul,ok 1#u32⟩

theorem step (flat : Slice U32) (prefixes : alloc.vec.Vec U32) (product : U32) (index : Usize) :
    NEW_GeometryActual.verifier.batch_prefix_products_loop.body flat prefixes product index =
      Port4C_NativePrefix.verifier.batch_prefix_products_loop.body leaves flat prefixes product index := by
  simp only [NEW_GeometryActual.verifier.batch_prefix_products_loop.body,
    Port4C_NativePrefix.verifier.batch_prefix_products_loop.body,leaves,
    NFN_NEW_GeometryArithmetic.multiply_probe]

theorem loop (flat : Slice U32) (prefixes : alloc.vec.Vec U32) (product : U32) (index : Usize) :
    NEW_GeometryActual.verifier.batch_prefix_products_loop flat prefixes product index =
      Port4C_NativePrefix.verifier.batch_prefix_products_loop leaves flat prefixes product index := by
  unfold NEW_GeometryActual.verifier.batch_prefix_products_loop
    Port4C_NativePrefix.verifier.batch_prefix_products_loop
  simp only [step]

theorem complete (flat : Slice U32) : NEW_GeometryActual.verifier.batch_prefix_products flat =
    Port4C_NativePrefix.verifier.batch_prefix_products leaves flat := by
  simp only [NEW_GeometryActual.verifier.batch_prefix_products,
    Port4C_NativePrefix.verifier.batch_prefix_products,leaves,
    NEW_GeometryActual.aspis_core.field.M31.ONE,bind_tc_ok,loop]

#print axioms step
#print axioms loop
#print axioms complete
end NFN_NEW_GeometryPrefix
-- END copied NEW_GeometryPrefix
-- BEGIN copied NEB_ActualGeometryPoint: evidence/slice-q-compose-20261029/NEB_ActualGeometryPoint.lean
set_option autoImplicit false
namespace NFN_NEB_ActualGeometryPoint
open Aeneas Aeneas.Std Result AspisR1 AspisR1QueryGeometryActual

/-- The actual selected table reads establish both product domains; the
original deployed-cohort dictionary is used in the returned point equation. -/
theorem calls (u : Usize) (admitted : NFN_NEA_PointBridge.PacketDomain u) :
    ∃ (iA iB : Usize) (a b : U32 × U32) (z : field.CM31),
      lift (u &&& 511#usize)=ok iA ∧ u >>> 9#i32=ok iB ∧
      Array.index_usize fast_domain.TABLE_A iA=ok a ∧
      Array.index_usize fast_domain.TABLE_B iB=ok b ∧
      NFN_NEA_FieldProduct.Canonical ⟨a.1,a.2⟩ ∧ NFN_NEA_FieldProduct.Canonical ⟨b.1,b.2⟩ ∧
      NFN_NEA_FieldProduct.ops.mul ⟨a.1,a.2⟩ ⟨b.1,b.2⟩=ok z ∧
      R17CurrentCM31Semantics.operations.mul ⟨a.1,a.2⟩ ⟨b.1,b.2⟩=ok z ∧
      NFN_NEA_FieldProduct.Canonical z ∧
      NEA_PointParam.point_ref u fast_domain.TABLE_A fast_domain.TABLE_B
        (Array.make 2#usize [z.a,z.b])=ok (NFN_NEA_PointBridge.record a b z) ∧
      fast_domain.fibre_point R17CurrentCM31Semantics.operations u=ok ⟨z.a,z.b⟩ := by
  obtain ⟨iA,iB,a,b,z,mask,shift,readA,readB,ca,cb,mul,cz,_⟩ :=
    NFN_NEB_PointCalls.selected_product u admitted
  have actual : R17CurrentCM31Semantics.operations.mul ⟨a.1,a.2⟩ ⟨b.1,b.2⟩=ok z :=
    (NFN_NEB_GeometryFieldPorts.cm_eq _ _ ca cb).trans mul
  have selected := NFN_NEA_PointBridge.selected R17CurrentCM31Semantics.operations u iA iB a b z
    mask shift readA readB (fun _ _ => rfl) actual
  exact ⟨iA,iB,a,b,z,mask,shift,readA,readB,ca,cb,mul,actual,cz,selected.1,selected.2⟩

theorem frame {S Event : Type} (state : S) (u : Usize) (admitted : NFN_NEA_PointBridge.PacketDomain u) :
    ∃ point : domain.Point field.M31,
      fast_domain.fibre_point R17CurrentCM31Semantics.operations u=ok point ∧
      point.x.val<2147483647 ∧ point.y.val<2147483647 ∧
      NEB_PureFrame.run (Event:=Event) state
        (fast_domain.fibre_point R17CurrentCM31Semantics.operations u)=ok (point,state,[]) := by
  obtain ⟨_,_,_,_,z,_,_,_,_,_,_,_,_,cz,_,run⟩ := calls u admitted
  exact ⟨⟨z.a,z.b⟩,run,cz.1,cz.2,NEB_PureFrame.successful state _ _ run⟩

#print axioms calls
#print axioms frame
end NFN_NEB_ActualGeometryPoint
-- END copied NEB_ActualGeometryPoint
-- BEGIN copied NEB_GeometryDictionaryEq: evidence/slice-q-compose-20261029/NEB_GeometryDictionaryEq.lean
set_option autoImplicit false
namespace NFN_NEB_GeometryDictionaryEq
open Aeneas Aeneas.Std Result AspisR1 AspisR1QueryGeometryActual

theorem point (u : Usize) :
    fast_domain.fibre_point R17CurrentCM31Semantics.operations u=
      fast_domain.fibre_point NFN_NEA_FieldProduct.ops u := by
  unfold fast_domain.fibre_point
  simp only [domain.FibreIndex.get,lift,bind_tc_ok]
  generalize readA : Array.index_usize fast_domain.TABLE_A (u &&& 511#usize)=ra
  cases ra with
  | fail e => rfl
  | div => rfl
  | ok a =>
    simp only [bind_tc_ok]
    rw [show fast_domain.table_value R17CurrentCM31Semantics.operations a=ok ⟨a.1,a.2⟩ from by cases a;rfl,
        show fast_domain.table_value NFN_NEA_FieldProduct.ops a=ok ⟨a.1,a.2⟩ from by cases a;rfl]
    simp only [bind_tc_ok]
    generalize shift : u >>> 9#i32=shifted
    cases shifted with
    | fail e => rfl
    | div => rfl
    | ok iB =>
      simp only [bind_tc_ok]
      generalize readB : Array.index_usize fast_domain.TABLE_B iB=rb
      cases rb with
      | fail e => rfl
      | div => rfl
      | ok b =>
        simp only [bind_tc_ok]
        rw [show fast_domain.table_value R17CurrentCM31Semantics.operations b=ok ⟨b.1,b.2⟩ from by cases b;rfl,
            show fast_domain.table_value NFN_NEA_FieldProduct.ops b=ok ⟨b.1,b.2⟩ from by cases b;rfl]
        simp only [bind_tc_ok]
        have ca := NEA_TableCanonical.readA (u &&& 511#usize)
          (NFN_NEB_PointSuccess.read_bound _ _ _ readA) a readA
        have cb := NEA_TableCanonical.readB iB (NFN_NEB_PointSuccess.read_bound _ _ _ readB) b readB
        rw [NFN_NEB_GeometryFieldPorts.cm_eq ⟨a.1,a.2⟩ ⟨b.1,b.2⟩ ca cb]

theorem line (u : Usize) :
    R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations u=
      R17FibrePointLineNodeActual.line_node NFN_NEA_FieldProduct.ops R17CurrentM31Semantics.operations u := by
  unfold R17FibrePointLineNodeActual.line_node
  rw [point]

theorem point_success (u : Usize) (p : domain.Point field.M31)
    (run : fast_domain.fibre_point R17CurrentCM31Semantics.operations u=ok p) :
    p.x.val<2147483647 ∧ p.y.val<2147483647 := by
  rw [point] at run
  exact NFN_NEB_PointSuccess.canonical u p run

theorem line_success (u : Usize) (out : U32)
    (run : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations
      R17CurrentM31Semantics.operations u=ok out) : out.val<2147483647 := by
  rw [line] at run
  exact NFN_NEB_LineCalls.successful u out run

#print axioms point
#print axioms line
#print axioms point_success
#print axioms line_success
end NFN_NEB_GeometryDictionaryEq
-- END copied NEB_GeometryDictionaryEq
-- BEGIN copied NEB_GeometryGatherDomains: evidence/slice-q-compose-20261029/NEB_GeometryGatherDomains.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NEB_GeometryGatherDomains
open Aeneas Aeneas.Std Result ControlFlow AspisR1 AspisR1Stage2
open Port3_NativeGeometryBody

theorem step {CoreError : Type} (ops : Ops CoreError) (error : CoreError) (start : Usize)
    (iter iter1 iterOut : core.slice.iter.Iter U32) (query : U32)
    (zs zsOut flat flatOut : alloc.vec.Vec U32)
    (next : core.slice.iter.IteratorSliceIter.next iter=ok (some query,iter1))
    (run : verifier.QueryGeometry.for_range_loop0.body
      (Port4C_GeometryStd.install (NFN_NEB_GeometryIndices.install ops error))
      start iter zs flat=ok (cont (iterOut,zsOut,flatOut))) :
    ∃ (r : Port4C_GeometryGather.Row) (u parent left right fibre fleft fright : Usize)
      (point : aspis_core.r0.domain.Point U32) (square doubled one : U32),
      iterOut=iter1 ∧
      lift (UScalar.cast .Usize query)=ok u ∧
      NFN_NEB_GeometryIndices.indexPort error u=ok (.Ok fibre) ∧ fibre=u ∧ fibre.val<262144 ∧
      (NFN_NEB_GeometryIndices.install ops error).op15 fibre=ok point ∧
      point.x.val<2147483647 ∧ point.y.val<2147483647 ∧
      u/4#usize=ok parent ∧ left=Usize.wrapping_mul parent 4#usize ∧
      NFN_NEB_GeometryIndices.indexPort error left=ok (.Ok fleft) ∧ fleft=left ∧ fleft.val<262144 ∧
      (NFN_NEB_GeometryIndices.install ops error).op14 fleft=ok r.lineX ∧ r.lineX.val<2147483647 ∧
      right=Usize.wrapping_add left 3#usize ∧
      NFN_NEB_GeometryIndices.indexPort error right=ok (.Ok fright) ∧ fright=right ∧ fright.val<262144 ∧
      (NFN_NEB_GeometryIndices.install ops error).op14 fright=ok r.lineY ∧ r.lineY.val<2147483647 ∧
      r.x=point.x ∧ r.y=point.y ∧
      (NFN_NEB_GeometryIndices.install ops error).op9 r.lineX r.lineX=ok square ∧ square.val<2147483647 ∧
      (NFN_NEB_GeometryIndices.install ops error).op10 square=ok doubled ∧ doubled.val<2147483647 ∧
      (NFN_NEB_GeometryIndices.install ops error).op7=ok one ∧ one.val<2147483647 ∧
      (NFN_NEB_GeometryIndices.install ops error).op8 doubled one=ok r.lineZ ∧ r.lineZ.val<2147483647 ∧
      (∀ x ∈ r.words, x≠0#u32) ∧
      flatOut.val=flat.val++r.words ∧ zsOut.val=zs.val++[r.lineZ] := by
  obtain ⟨r,u,parent,left,right,fibre,fleft,fright,point,square,doubled,one,fields⟩ :=
    Port4C_GeometryGather.step (NFN_NEB_GeometryIndices.install ops error) start
      iter iter1 iterOut query zs zsOut flat flatOut next run
  rcases fields with ⟨it,cast,new,pointRun,division,leftEq,newLeft,lineX,rightEq,newRight,lineY,hx,hy,mul,dbl,unit,sub,raw,append,zsEq⟩
  have fi := NFN_NEB_GeometryIndices.accepted error u fibre new
  have fl := NFN_NEB_GeometryIndices.accepted error left fleft newLeft
  have fr := NFN_NEB_GeometryIndices.accepted error right fright newRight
  have leaves := NFN_NEB_GeometryIndices.primitives ops error
  have cp := leaves.point _ _ pointRun
  have cx := leaves.line _ _ lineX
  have cy := leaves.line _ _ lineY
  have cs := leaves.multiply _ _ _ cx cx mul
  have cd := leaves.double _ _ cs dbl
  have co := leaves.one _ unit
  have cz := leaves.subtract _ _ _ cd co sub
  exact ⟨r,u,parent,left,right,fibre,fleft,fright,point,square,doubled,one,
    it,cast,new,fi.1,fi.2,pointRun,cp.1,cp.2,division,leftEq,newLeft,fl.1,fl.2,lineX,cx,
    rightEq,newRight,fr.1,fr.2,lineY,cy,hx,hy,mul,cs,dbl,cd,unit,co,sub,cz,raw,append,zsEq⟩

theorem traversal {CoreError : Type} (ops : Ops CoreError) (error : CoreError)
    (start : Usize) (iter : core.slice.iter.Iter U32) (zs flat : alloc.vec.Vec U32)
    (out : verifier.QueryGeometry) (fuel : Nat)
    (remaining : iter.i+fuel=iter.slice.val.length)
    (canonical : ∀ x ∈ flat.val, Port5Q1_GeometryCanonical.Canonical x)
    (raw : ∀ x ∈ flat.val, x≠0#u32)
    (run : verifier.QueryGeometry.for_range_loop0
      (Port4C_GeometryStd.install (NFN_NEB_GeometryIndices.install ops error))
      iter start zs flat=ok (.Ok out)) :
    ∃ zsFinal flatFinal terminal,
      (∀ x ∈ flatFinal.val, Port5Q1_GeometryCanonical.Canonical x) ∧
      (∀ x ∈ flatFinal.val, x≠0#u32) ∧
      verifier.QueryGeometry.for_range_loop0.body
        (Port4C_GeometryStd.install (NFN_NEB_GeometryIndices.install ops error))
        start terminal zsFinal flatFinal=ok (done (.Ok out)) ∧
      terminal.i=terminal.slice.val.length ∧
      zsFinal.val.length=zs.val.length+fuel ∧ flatFinal.val.length=flat.val.length+5*fuel :=
  Port5Q1_GeometryCanonical.traversal _ (NFN_NEB_GeometryIndices.primitives ops error)
    start iter zs flat out fuel remaining canonical raw run

#print axioms step
#print axioms traversal
end NFN_NEB_GeometryGatherDomains
end
-- END copied NEB_GeometryGatherDomains
-- BEGIN copied NEB_GeometryModel: evidence/slice-q-compose-20261029/NEB_GeometryModel.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NEB_GeometryModel
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeGeometryBody

def install {CoreError : Type} (ops : Ops CoreError) (error : CoreError) : Ops CoreError :=
  {NFN_NEB_GeometryIndices.install ops error with op11:=Port4C_InverseExecution.inverse_owned}

theorem primitives {CoreError : Type} (ops : Ops CoreError) (error : CoreError) :
    Port5Q1_GeometryCanonical.SessionAPrimitives (install ops error) := by
  have p := NFN_NEB_GeometryIndices.primitives ops error
  exact ⟨p.point,p.line,p.multiply,p.double,p.one,p.subtract⟩

/-- All inner canonical primitive predicates and the chosen inverse operation
are instantiated. The premise is the SAME adopted model parent success, not
an additional prefix/inverse/collect success premise or a native claim. -/
theorem for_range {CoreError : Type} (ops : Ops CoreError) (error : CoreError)
    (queries : Array U32 22#usize) (start end1 : Usize) (out : verifier.QueryGeometry)
    (nonempty : start.val<end1.val)
    (accepted : Port3_GeometryStage.geometry
      (Port5Q1_GeometryTerminal.install (install ops error)) queries start end1=ok (.Ok out)) :
    ∃ flat inverse : alloc.vec.Vec U32,
      out.start=start ∧ out.line_z.val.length=end1.val-start.val ∧
      flat.val.length=5*(end1.val-start.val) ∧
      (∀ x ∈ flat.val, Port5Q1_GeometryCanonical.Canonical x) ∧
      (∀ x ∈ flat.val, S7JoinBasisMachine.decode x≠0) ∧
      inverse.val.length=flat.val.length ∧
      (∀ j, j<flat.val.length →
        S7JoinBasisMachine.decode (Port4C_BatchInverse.cell inverse.val j)=
          (S7JoinBasisMachine.decode (Port4C_BatchInverse.cell flat.val j))⁻¹) ∧
      out.inverses.val=(List.range (end1.val-start.val)).map (Port4C_CollectLoop.record inverse) :=
  Port5Q1_Geometry.for_range (install ops error) (primitives ops error) rfl rfl rfl
    queries start end1 out nonempty accepted

#print axioms primitives
#print axioms for_range
end NFN_NEB_GeometryModel
end
-- END copied NEB_GeometryModel
-- BEGIN copied NEB_ActualGeometryModel: evidence/slice-q-compose-20261029/NEB_ActualGeometryModel.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NEB_ActualGeometryModel
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeGeometryBody

/-- The actual R17 point/line dictionary, with the checked index reference and
inverse body already selected in the adopted geometry model. This is a model
installation, not a substitute for the missing frozen native root bridge. -/
def install {CoreError : Type} (ops : Ops CoreError) (error : CoreError) : Ops CoreError :=
  {NFN_NEB_GeometryModel.install ops error with
    op15 := fun f => do
      let p ← AspisR1QueryGeometryActual.fast_domain.fibre_point R17CurrentCM31Semantics.operations f
      ok ⟨p.x,p.y⟩
    op14 := R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations}

theorem same_dictionary {CoreError : Type} (ops : Ops CoreError) (error : CoreError) :
    install ops error = NFN_NEB_GeometryModel.install ops error := by
  have hp : (fun f => do
      let p ← AspisR1QueryGeometryActual.fast_domain.fibre_point R17CurrentCM31Semantics.operations f
      ok ({x:=p.x,y:=p.y} : aspis_core.r0.domain.Point U32)) =
    (fun f => do
      let p ← AspisR1QueryGeometryActual.fast_domain.fibre_point NFN_NEA_FieldProduct.ops f
      ok ({x:=p.x,y:=p.y} : aspis_core.r0.domain.Point U32)) := by
    funext f
    rw [NFN_NEB_GeometryDictionaryEq.point]
  have hl := funext NFN_NEB_GeometryDictionaryEq.line
  unfold install
  rw [hp,hl]
  rfl

theorem primitives {CoreError : Type} (ops : Ops CoreError) (error : CoreError) :
    Port5Q1_GeometryCanonical.SessionAPrimitives (install ops error) := by
  rw [same_dictionary]
  exact NFN_NEB_GeometryModel.primitives ops error

/-- Every non-root canonical primitive premise is discharged for the actual
R17 dictionary. The sole success premise is the same parent model Result. -/
theorem for_range {CoreError : Type} (ops : Ops CoreError) (error : CoreError)
    (queries : Array U32 22#usize) (start end1 : Usize) (out : verifier.QueryGeometry)
    (nonempty : start.val<end1.val)
    (accepted : Port3_GeometryStage.geometry
      (Port5Q1_GeometryTerminal.install (install ops error)) queries start end1=ok (.Ok out)) :
    ∃ flat inverse : alloc.vec.Vec U32,
      out.start=start ∧ out.line_z.val.length=end1.val-start.val ∧
      flat.val.length=5*(end1.val-start.val) ∧
      (∀ x ∈ flat.val, Port5Q1_GeometryCanonical.Canonical x) ∧
      (∀ x ∈ flat.val, S7JoinBasisMachine.decode x≠0) ∧
      inverse.val.length=flat.val.length ∧
      (∀ j, j<flat.val.length →
        S7JoinBasisMachine.decode (Port4C_BatchInverse.cell inverse.val j)=
          (S7JoinBasisMachine.decode (Port4C_BatchInverse.cell flat.val j))⁻¹) ∧
      out.inverses.val=(List.range (end1.val-start.val)).map (Port4C_CollectLoop.record inverse) := by
  rw [same_dictionary] at accepted
  exact NFN_NEB_GeometryModel.for_range ops error queries start end1 out nonempty accepted

#print axioms same_dictionary
#print axioms primitives
#print axioms for_range
end NFN_NEB_ActualGeometryModel
end
-- END copied NEB_ActualGeometryModel
-- BEGIN copied NEW_GeometryRawInterface: evidence/slice-q-compose4-20261104/NEW_GeometryRawInterface.lean
set_option autoImplicit false
namespace NFN_NEW_GeometryRawInterface
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
 mapIterator := fun it f => {next := core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next it f}

#print axioms geometry_roundtrip
#print axioms geometry_reverse
#print axioms error_roundtrip
#print axioms error_reverse
#print axioms answer_roundtrip
#print axioms answer_reverse
#print axioms ops
end NFN_NEW_GeometryRawInterface
-- END copied NEW_GeometryRawInterface
-- BEGIN copied NEW_GeometryRawHelpers: evidence/slice-q-compose4-20261104/NEW_GeometryRawHelpers.lean
set_option autoImplicit false
namespace NFN_NEW_GeometryRawHelpers
open Aeneas Aeneas.Std Result AspisR1 NFN_NEW_GeometryRawInterface

theorem zero_callback : NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool = Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool ops := by rfl

theorem inner_callback : NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 = Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 ops := by rfl

theorem outer_callback : NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 = Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 ops := by rfl

theorem clone : NEW_GeometryActual.aspis_core.field.M31.Insts.CoreCloneClone =
    core.marker.CopyU32.cloneInst := by rfl

theorem backward_body (flat prefixes : alloc.vec.Vec U32)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (suffix : U32) (inverse : alloc.vec.Vec U32) :
    NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0_loop0.body flat prefixes iter suffix inverse =
      Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0.body
        ops flat prefixes iter suffix inverse := by rfl

theorem backward (flat prefixes : alloc.vec.Vec U32)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (suffix : U32) (inverse : alloc.vec.Vec U32) :
    NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0_loop0 iter flat prefixes suffix inverse =
      Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0
        ops iter flat prefixes suffix inverse := by rfl

#print axioms zero_callback
#print axioms inner_callback
#print axioms outer_callback
#print axioms clone
#print axioms backward_body
#print axioms backward
end NFN_NEW_GeometryRawHelpers
-- END copied NEW_GeometryRawHelpers
-- BEGIN copied NEW_GeometryRawBody: evidence/slice-q-compose4-20261104/NEW_GeometryRawBody.lean
set_option autoImplicit false
namespace NFN_NEW_GeometryRawBody
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NEW_GeometryRawInterface NFN_NEW_GeometryRawHelpers
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
abbrev State := core.slice.iter.Iter U32 × alloc.vec.Vec U32 × alloc.vec.Vec U32

theorem map_iterator {B I F Item : Type} (it : core.iter.traits.iterator.Iterator I Item)
    (f : core.ops.function.FnMut F Item B) :
    NEW_GeometryActual.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator it f = ops.mapIterator it f := by
  rfl

theorem bind_congr {A B : Type} (m : Result A) (k l : A → Result B)
    (h : ∀ a, k a=l a) : (m >>= k) = (m >>= l) := by
  exact congrArg (fun k => m >>= k) (funext h)

/-- Exact one-body Result conversion on the SAME iterator and both Vecs.
All child operations are the concrete emitted dictionary, with no free replies. -/
theorem step (start : Usize) (iter : core.slice.iter.Iter U32)
    (lines flat : alloc.vec.Vec U32) :
    resultMap (NEW_LoopMap.flowMap answer)
      (NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0.body start iter lines flat) =
      Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body ops start iter lines flat := by
  simp only [NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0.body,
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body,
    resultMap_bind,NEW_LoopMap.map_ok,NEW_LoopMap.flowMap,
    ←zero_callback,←outer_callback,←backward,←clone,←map_iterator]
  simp only [ops,bind_assoc_eq,bind_tc_ok,apply_ite,NEW_LoopMap.map_ok,
    NEW_LoopMap.flowMap,answer,geometry,error]
  congr 1
  funext following
  rcases following with ⟨query,iter1⟩
  all_goals
    repeat' first
    | rfl
    | simp only [uncurry,resultMap_bind,NEW_LoopMap.map_ok,NEW_LoopMap.flowMap,
        answer,geometry,error,bind_assoc_eq,bind_tc_ok,←clone,←map_iterator,
        alloc.vec.Vec.is_empty,core.result.Result.map_err,Port4C_GeometryStd.mapError,
        NEW_GeometryActual.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError,
        NEW_GeometryActual.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
        NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError,
        NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
        NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError,
        NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
        Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError,
        Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
        Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError,
        Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
        Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError,
        Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
    | (apply bind_congr; intro)
    | split

#print axioms map_iterator
#print axioms bind_congr
#print axioms step
end NFN_NEW_GeometryRawBody
-- END copied NEW_GeometryRawBody
-- BEGIN copied NEW_GeometryRawRoot: evidence/slice-q-compose4-20261104/NEW_GeometryRawRoot.lean
set_option autoImplicit false
namespace NFN_NEW_GeometryRawRoot
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NEW_GeometryRawInterface NFN_NEW_GeometryRawBody
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

def body (start : Usize) (s : State) :=
  let (it,lines,flat) := s
  NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0.body start it lines flat

theorem complete_loop (start : Usize) (iter : core.slice.iter.Iter U32)
    (lines flat : alloc.vec.Vec U32) :
    resultMap answer (NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0 iter start lines flat) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0 ops iter start lines flat := by
  unfold NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0
  change resultMap answer (loop (body start) (iter,lines,flat)) = _
  rw [NEW_LoopMap.complete (body start) answer answerBack answer_roundtrip answer_reverse]
  congr 1
  funext s
  rcases s with ⟨it,ls,fl⟩
  exact step start it ls fl

/-- Full emitted actual root: every rejection, failure and divergence as well
as every lane of the successful geometry; no acceptance premise. -/
theorem complete (queries : Array U32 22#usize) (start finish : Usize) :
    resultMap answer (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range ops queries start finish := by
  unfold NEW_GeometryActual.verifier.QueryGeometry.for_range
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range
  repeat' first
  | rfl
  | simp only [apply_ite,resultMap_bind,NEW_LoopMap.map_ok,answer,geometry,error,complete_loop]
  | (apply bind_congr; intro)
  | split

#print axioms body
#print axioms complete_loop
#print axioms complete
end NFN_NEW_GeometryRawRoot
-- END copied NEW_GeometryRawRoot
-- BEGIN copied NEW_GeometryPointPrimitives: evidence/slice-q-compose4-20261104/NEW_GeometryPointPrimitives.lean
set_option autoImplicit false
namespace NFN_NEW_GeometryPointPrimitives
open Aeneas Aeneas.Std Result AspisR1
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
abbrev C := NEW_GeometryActual.aspis_core.field.CM31
abbrev G := AspisR1QueryGeometryActual.field.CM31
abbrev P := NEW_GeometryActual.aspis_core.r0.domain.Point U32
abbrev GP := AspisR1QueryGeometryActual.domain.Point U32

def toG (x : C) : G := ⟨x.a,x.b⟩
def toP (p : P) : GP := ⟨p.x,p.y⟩

theorem cm_multiply (x y : C) :
    resultMap toG (NEW_GeometryActual.aspis_core.field.CM31.mul x y) =
      NFN_NEA_FieldProduct.ops.mul (toG x) (toG y) := by
  change resultMap toG (NEW_GeometryActual.aspis_core.field.CM31.mul x y) =
    (do let z ← FIo_Native.aspis_core.field.CM31.mul
          (NFN_NEW_GeometryArithmetic.toC x) (NFN_NEW_GeometryArithmetic.toC y)
        ok (NFN_NEA_FieldProduct.ofNative z))
  rw [←NFN_NEW_GeometryArithmetic.cm_multiply]
  cases NEW_GeometryActual.aspis_core.field.CM31.mul x y <;> rfl

/-- Identical literal frozen tables, not a new field enumeration or exponent proof. -/
theorem tableA : NEW_GeometryActual.fast_domain.TABLE_A =
    AspisR1QueryGeometryActual.fast_domain.TABLE_A := by
  NEW_literal_refl

theorem tableB : NEW_GeometryActual.fast_domain.TABLE_B =
    AspisR1QueryGeometryActual.fast_domain.TABLE_B := by
  NEW_literal_refl

theorem table_value (p : U32 × U32) :
    resultMap toG (NEW_GeometryActual.fast_domain.table_value p) =
      AspisR1QueryGeometryActual.fast_domain.table_value NFN_NEA_FieldProduct.ops p := by
  cases p
  rfl

#print axioms cm_multiply
#print axioms tableA
#print axioms tableB
#print axioms table_value
end NFN_NEW_GeometryPointPrimitives
-- END copied NEW_GeometryPointPrimitives
-- BEGIN copied NEW_GeometryPoint: evidence/slice-q-compose4-20261104/NEW_GeometryPoint.lean
set_option autoImplicit false
namespace NFN_NEW_GeometryPoint
open Aeneas Aeneas.Std Result AspisR1
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
open NFN_NEW_GeometryPointPrimitives

theorem map_point_ok (x y : U32) :
    resultMap toP (ok ({x,y} : P)) = ok ({x,y} : GP) := rfl

/-- Entire point Result for every alias index. Both actual table reads and
both failure/divergence branches are preserved. No child-success premise. -/
theorem complete (u : Usize) :
    resultMap toP (NEW_GeometryActual.fast_domain.fibre_point u) =
      AspisR1QueryGeometryActual.fast_domain.fibre_point NFN_NEA_FieldProduct.ops u := by
  simp only [NEW_GeometryActual.fast_domain.fibre_point,
    AspisR1QueryGeometryActual.fast_domain.fibre_point,
    NEW_GeometryActual.aspis_core.r0.domain.FibreIndex.get,
    AspisR1QueryGeometryActual.domain.FibreIndex.get,
    resultMap_bind,map_point_ok,lift,bind_tc_ok,tableA,tableB,
    NEW_ShiftAssociation.checked_to_wrapping]
  generalize ha : Array.index_usize AspisR1QueryGeometryActual.fast_domain.TABLE_A
    (u &&& 511#usize) = a
  cases a with
  | fail e => rfl
  | div => rfl
  | ok a =>
    simp only [bind_tc_ok]
    generalize hb : Array.index_usize AspisR1QueryGeometryActual.fast_domain.TABLE_B
      (Usize.wrapping_shr u 9#u32) = b
    cases b with
    | fail e => rfl
    | div => rfl
    | ok b =>
      rcases a with ⟨a0,a1⟩
      rcases b with ⟨b0,b1⟩
      simp only [NEW_GeometryActual.fast_domain.table_value,
        NEW_GeometryActual.aspis_core.field.CM31.new,
        AspisR1QueryGeometryActual.fast_domain.table_value,NFN_NEA_FieldProduct.ops,
        NFN_NEA_FieldProduct.toNative,NFN_NEA_FieldProduct.ofNative,bind_tc_ok,map_point_ok]
      try dsimp only
      simp only [bind_tc_ok,bind_assoc_eq]
      change (do let c ← NEW_GeometryActual.aspis_core.field.CM31.mul
                    ({a:=a0,b:=a1} : NFN_NEW_GeometryPointPrimitives.C)
                    ({a:=b0,b:=b1} : NFN_NEW_GeometryPointPrimitives.C)
                 ok ({x:=c.a,y:=c.b} : GP)) =
        (do let c ← FIo_Native.aspis_core.field.CM31.mul ⟨a0,a1⟩ ⟨b0,b1⟩
            ok ({x:=c.a,y:=c.b} : GP))
      have product := NFN_NEW_GeometryArithmetic.cm_multiply
        ({a:=a0,b:=a1} : NFN_NEW_GeometryPointPrimitives.C)
        ({a:=b0,b:=b1} : NFN_NEW_GeometryPointPrimitives.C)
      simp only [NFN_NEW_GeometryArithmetic.toC] at product
      rw [←product]
      cases NEW_GeometryActual.aspis_core.field.CM31.mul
        ({a:=a0,b:=a1} : NFN_NEW_GeometryPointPrimitives.C)
        ({a:=b0,b:=b1} : NFN_NEW_GeometryPointPrimitives.C) <;> rfl

#print axioms map_point_ok
#print axioms complete
end NFN_NEW_GeometryPoint
-- END copied NEW_GeometryPoint
-- BEGIN copied NEW_GeometryChildren: evidence/slice-q-compose4-20261104/NEW_GeometryChildren.lean
set_option autoImplicit false
namespace NFN_NEW_GeometryChildren
open Aeneas Aeneas.Std Result AspisR1
open NFN_NEW_GeometryRawInterface NFN_NEW_GeometryPointPrimitives
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

theorem bind_map {A B T : Type} (f : A → B) (r : Result A) (k : B → Result T) :
    (resultMap f r >>= k) = (r >>= fun a => k (f a)) := by cases r <;> rfl

theorem point (u : Usize) : ops.op15 u =
    (NFN_NEB_GeometryPrimitives.install ops).op15 u := by
  have h := congrArg (fun r : Result GP => do
    let p ← r
    ok ({x:=p.x,y:=p.y} : AspisR1Stage2.aspis_core.r0.domain.Point U32))
      (NFN_NEW_GeometryPoint.complete u)
  simpa only [bind_map,bind_tc_ok,toP,ops,NFN_NEB_GeometryPrimitives.install] using h

theorem line (u : Usize) : NEW_GeometryActual.fast_domain.line_node u =
    R17FibrePointLineNodeActual.line_node NFN_NEA_FieldProduct.ops R17CurrentM31Semantics.operations u := by
  have h := congrArg (fun r : Result GP => do
    let p ← r
    NFN_NEW_GeometryPolynomial.cohort p.x) (NFN_NEW_GeometryPoint.complete u)
  have contextual : NEW_GeometryActual.fast_domain.line_node u =
      (do let p ← NEW_GeometryActual.fast_domain.fibre_point u
          NFN_NEW_GeometryPolynomial.cohort p.x) := by
    change (do let p ← NEW_GeometryActual.fast_domain.fibre_point u
               NFN_NEW_GeometryPolynomial.native p.x) = _
    simp only [NFN_NEW_GeometryPolynomial.complete]
  rw [contextual]
  change (do let p ← NEW_GeometryActual.fast_domain.fibre_point u
             NFN_NEW_GeometryPolynomial.cohort p.x) =
    (do let p ← AspisR1QueryGeometryActual.fast_domain.fibre_point NFN_NEA_FieldProduct.ops u
        NFN_NEW_GeometryPolynomial.cohort p.x)
  simpa only [bind_map,bind_tc_ok,toP] using h

theorem index (u : Usize) : NEW_GeometryActual.aspis_core.r0.domain.FibreIndex.new u =
    NFN_NEB_GeometryIndices.indexPort NEW_GeometryActual.aspis_core.r0.Error.IndexOutOfRange u := by
  simp only [NEW_GeometryActual.aspis_core.r0.domain.FibreIndex.new,
    NEW_GeometryActual.aspis_core.r0.FIBRE_COUNT,bind_tc_ok,
    NFN_NEB_GeometryIndices.indexPort,NEA_Reference.fibre_new_ref]
  split <;> rfl

#print axioms bind_map
#print axioms point
#print axioms line
#print axioms index
end NFN_NEW_GeometryChildren
-- END copied NEW_GeometryChildren
-- BEGIN copied NEW_GeometryDictionary: evidence/slice-q-compose4-20261104/NEW_GeometryDictionary.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NEW_GeometryDictionary
open Aeneas Aeneas.Std Result AspisR1
open NFN_NEW_GeometryRawInterface
abbrev CE := NEW_GeometryActual.aspis_core.r0.Error
abbrev err : CE := .IndexOutOfRange

def adopted : Port3_NativeGeometryBody.Ops CE :=
  Port5Q1_GeometryTerminal.install (NFN_NEB_ActualGeometryModel.install ops err)

def contextual : Port3_NativeGeometryBody.Ops CE :=
  {adopted with op8:=ops.op8,op10:=ops.op10}

/-- All children except the domain-dependent double/sub slots have universal
full Result correspondences; those two are replaced only in their real context. -/
theorem dictionary : ops = contextual := by
  unfold contextual adopted
  rw [NFN_NEB_ActualGeometryModel.same_dictionary]
  unfold NFN_NEB_GeometryModel.install NFN_NEB_GeometryIndices.install
    NFN_NEB_GeometryPrimitives.install Port5Q1_GeometryTerminal.install
    Port4C_CollectStd.install Port4C_GeometryGroups.install
    Port4C_GeometryInverse.install Port4C_GeometryStd.install
  unfold ops
  dsimp only
  congr 1
  all_goals try rfl
  all_goals try simp only [NEW_GeometryActual.aspis_core.field.M31.ZERO,NEW_GeometryActual.aspis_core.field.M31.ONE]
  all_goals try exact funext (fun x => funext (NFN_NEW_GeometryArithmetic.multiply_probe x))
  all_goals try exact funext NFN_NEW_GeometryArithmetic.multiply_probe
  all_goals try exact funext NFN_NEW_GeometryArithmetic.inverse
  all_goals try exact funext NFN_NEW_GeometryChildren.index
  all_goals try exact funext NFN_NEW_GeometryPrefix.complete
  all_goals try exact funext NFN_NEW_GeometryChildren.line
  all_goals try exact funext NFN_NEW_GeometryChildren.point

#print axioms adopted
#print axioms contextual
#print axioms dictionary
end NFN_NEW_GeometryDictionary
end
-- END copied NEW_GeometryDictionary
-- BEGIN copied NEW_GeometryContextGeneric: evidence/slice-q-compose4-20261104/NEW_GeometryContextGeneric.lean
set_option autoImplicit false
namespace NFN_NEW_GeometryContextGeneric
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NEW_GeometryRawBody
variable {CE : Type}

def replace (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) : Port3_NativeGeometryBody.Ops CE :=
  {o with op8:=sub,op10:=double}

theorem reverse (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32)
    (it : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (flat pref : alloc.vec.Vec U32) (suffix : U32) (inv : alloc.vec.Vec U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0 (replace o sub double) it flat pref suffix inv =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0 o it flat pref suffix inv := by rfl

theorem zero_callback (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool (replace o sub double) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool o := by rfl

theorem collect_callback (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 (replace o sub double) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 o := by rfl

theorem error_callback0 (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError (replace o sub double) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError o := by rfl

theorem error_callback1 (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError (replace o sub double) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError o := by rfl

theorem error_callback2 (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError (replace o sub double) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError o := by rfl

/-- Generic one-body congruence. Its sole arithmetic premise is a contextual
three-call law, later discharged without a parent-success assumption. -/
theorem step (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32)
    (poly : ∀ (T : Type) (x : U32) (k : U32 → Result T),
      (do let p ← o.op9 x x; let d ← double p; let one ← o.op7; let z ← sub d one; k z) =
      (do let p ← o.op9 x x; let d ← o.op10 p; let one ← o.op7; let z ← o.op8 d one; k z))
    (start : Usize) (iter : core.slice.iter.Iter U32) (lines flat : alloc.vec.Vec U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body (replace o sub double) start iter lines flat =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body o start iter lines flat := by
  simp only [Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body,
    reverse,zero_callback,collect_callback,error_callback0,error_callback1,error_callback2]
  simp only [replace,bind_assoc_eq,bind_tc_ok]
  conv_lhs =>
    pattern (o.op9 _ _ >>= _)
    rw [poly]

#print axioms replace
#print axioms reverse
#print axioms zero_callback
#print axioms collect_callback
#print axioms error_callback0
#print axioms error_callback1
#print axioms error_callback2
#print axioms step
end NFN_NEW_GeometryContextGeneric
-- END copied NEW_GeometryContextGeneric
-- BEGIN copied NEW_GeometryContext: evidence/slice-q-compose4-20261104/NEW_GeometryContext.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NEW_GeometryContext
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NEW_GeometryRawInterface NFN_NEW_GeometryRawBody NFN_NEW_GeometryDictionary
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20


theorem one : adopted.op7=ok 1#u32 := by rfl
 theorem multiply : adopted.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul := by rfl
 theorem double : adopted.op10=AspisR1Qm31ArithmeticProbe.field.M31.double := by rfl
 theorem subtract : adopted.op8=AspisR1Qm31ArithmeticProbe.field.M31.sub := by rfl

theorem polynomial {T : Type} (x : U32) (k : U32 → Result T) :
 (do let p ← adopted.op9 x x
     let d ← ops.op10 p
     let one ← adopted.op7
     let z ← ops.op8 d one
     k z) =
 (do let p ← adopted.op9 x x
     let d ← adopted.op10 p
     let one ← adopted.op7
     let z ← adopted.op8 d one
     k z) := by
 simp only [one,multiply,double,subtract,ops,bind_tc_ok]
 simpa only [NFN_NEW_GeometryArithmetic.multiply_probe,NEW_GeometryActual.aspis_core.field.M31.ONE] using NFN_NEW_GeometryPolynomial.continuation x k

/-- Contextual replacement of only the two operations whose unrestricted raw
input specifications differ. The preceding product establishes their domains. -/
theorem step (start : Usize) (iter : core.slice.iter.Iter U32) (lines flat : alloc.vec.Vec U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body contextual start iter lines flat =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start iter lines flat := by
  exact NFN_NEW_GeometryContextGeneric.step adopted ops.op8 ops.op10
    (fun T x k => polynomial x k) start iter lines flat

#print axioms one
#print axioms multiply
#print axioms double
#print axioms subtract
#print axioms polynomial
#print axioms step
end NFN_NEW_GeometryContext
end
-- END copied NEW_GeometryContext

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
