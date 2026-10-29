import NEB_GeometryIndices
set_option autoImplicit false
noncomputable section
namespace NEB_GeometryGatherDomains
open Aeneas Aeneas.Std Result ControlFlow AspisR1 AspisR1Stage2
open Port3_NativeGeometryBody

theorem step {CoreError : Type} (ops : Ops CoreError) (error : CoreError) (start : Usize)
    (iter iter1 iterOut : core.slice.iter.Iter U32) (query : U32)
    (zs zsOut flat flatOut : alloc.vec.Vec U32)
    (next : core.slice.iter.IteratorSliceIter.next iter=ok (some query,iter1))
    (run : verifier.QueryGeometry.for_range_loop0.body
      (Port4C_GeometryStd.install (NEB_GeometryIndices.install ops error))
      start iter zs flat=ok (cont (iterOut,zsOut,flatOut))) :
    ∃ (r : Port4C_GeometryGather.Row) (u parent left right fibre fleft fright : Usize)
      (point : aspis_core.r0.domain.Point U32) (square doubled one : U32),
      iterOut=iter1 ∧
      lift (UScalar.cast .Usize query)=ok u ∧
      NEB_GeometryIndices.indexPort error u=ok (.Ok fibre) ∧ fibre=u ∧ fibre.val<262144 ∧
      (NEB_GeometryIndices.install ops error).op15 fibre=ok point ∧
      point.x.val<2147483647 ∧ point.y.val<2147483647 ∧
      u/4#usize=ok parent ∧ left=Usize.wrapping_mul parent 4#usize ∧
      NEB_GeometryIndices.indexPort error left=ok (.Ok fleft) ∧ fleft=left ∧ fleft.val<262144 ∧
      (NEB_GeometryIndices.install ops error).op14 fleft=ok r.lineX ∧ r.lineX.val<2147483647 ∧
      right=Usize.wrapping_add left 3#usize ∧
      NEB_GeometryIndices.indexPort error right=ok (.Ok fright) ∧ fright=right ∧ fright.val<262144 ∧
      (NEB_GeometryIndices.install ops error).op14 fright=ok r.lineY ∧ r.lineY.val<2147483647 ∧
      r.x=point.x ∧ r.y=point.y ∧
      (NEB_GeometryIndices.install ops error).op9 r.lineX r.lineX=ok square ∧ square.val<2147483647 ∧
      (NEB_GeometryIndices.install ops error).op10 square=ok doubled ∧ doubled.val<2147483647 ∧
      (NEB_GeometryIndices.install ops error).op7=ok one ∧ one.val<2147483647 ∧
      (NEB_GeometryIndices.install ops error).op8 doubled one=ok r.lineZ ∧ r.lineZ.val<2147483647 ∧
      (∀ x ∈ r.words, x≠0#u32) ∧
      flatOut.val=flat.val++r.words ∧ zsOut.val=zs.val++[r.lineZ] := by
  obtain ⟨r,u,parent,left,right,fibre,fleft,fright,point,square,doubled,one,fields⟩ :=
    Port4C_GeometryGather.step (NEB_GeometryIndices.install ops error) start
      iter iter1 iterOut query zs zsOut flat flatOut next run
  rcases fields with ⟨it,cast,new,pointRun,division,leftEq,newLeft,lineX,rightEq,newRight,lineY,hx,hy,mul,dbl,unit,sub,raw,append,zsEq⟩
  have fi := NEB_GeometryIndices.accepted error u fibre new
  have fl := NEB_GeometryIndices.accepted error left fleft newLeft
  have fr := NEB_GeometryIndices.accepted error right fright newRight
  have leaves := NEB_GeometryIndices.primitives ops error
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
      (Port4C_GeometryStd.install (NEB_GeometryIndices.install ops error))
      iter start zs flat=ok (.Ok out)) :
    ∃ zsFinal flatFinal terminal,
      (∀ x ∈ flatFinal.val, Port5Q1_GeometryCanonical.Canonical x) ∧
      (∀ x ∈ flatFinal.val, x≠0#u32) ∧
      verifier.QueryGeometry.for_range_loop0.body
        (Port4C_GeometryStd.install (NEB_GeometryIndices.install ops error))
        start terminal zsFinal flatFinal=ok (done (.Ok out)) ∧
      terminal.i=terminal.slice.val.length ∧
      zsFinal.val.length=zs.val.length+fuel ∧ flatFinal.val.length=flat.val.length+5*fuel :=
  Port5Q1_GeometryCanonical.traversal _ (NEB_GeometryIndices.primitives ops error)
    start iter zs flat out fuel remaining canonical raw run

#print axioms step
#print axioms traversal
end NEB_GeometryGatherDomains
end
