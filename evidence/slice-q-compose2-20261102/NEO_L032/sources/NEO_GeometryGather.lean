import NEO_GeometryScalarRef.Funs
import NEB_GeometryGatherDomains
set_option autoImplicit false
noncomputable section
namespace NEO_GeometryGather
open Aeneas Aeneas.Std Result ControlFlow AspisR1 AspisR1Stage2
open Port3_NativeGeometryBody

def dictionary {C : Type} (ops : Ops C) : NEO_GeometryScalarRef.Ops Unit where
 point := fun f => do let p ← ops.op15 f; ok (p.x,p.y)
 line := ops.op14
 mul := ops.op9
 double := ops.op10
 sub := ops.op8

/-- The independent reference reads the same checked query, same aligned line
operands, same product/double/subtraction replies, and five nonzero words of
one actual accepted emitted gather iteration. The remaining Vec operations
are not treated as native evidence by this theorem. -/
theorem accepted {C : Type} (ops : Ops C) (error : C) (start : Usize)
 (iter iter1 iterOut : core.slice.iter.Iter U32) (query : U32)
 (zs zsOut flat flatOut : alloc.vec.Vec U32)
 (next : core.slice.iter.IteratorSliceIter.next iter=ok (some query,iter1))
 (run : verifier.QueryGeometry.for_range_loop0.body
  (Port4C_GeometryStd.install (NEB_GeometryIndices.install ops error))
  start iter zs flat=ok (cont (iterOut,zsOut,flatOut))) :
 ∃ row : Array U32 5#usize,
  NEO_GeometryScalarRef.gather (dictionary (NEB_GeometryIndices.install ops error)) query =
   ok (.Ok row) ∧ flatOut.val=flat.val++row.val := by
 obtain ⟨r,u,parent,left,right,fibre,fleft,fright,point,square,doubled,one,
  it,cast,idx,fi,bound,pt,cx,cy,div,le,il,fl,bl,lx,clx,re,ir,fr,br,ly,cly,
  rx,ry,mul,cs,dbl,cd,unit,co,sub,cz,nonzero,append,zseq⟩ :=
  NEB_GeometryGatherDomains.step ops error start iter iter1 iterOut query zs zsOut flat flatOut next run
 have ne : r.x≠0#u32 ∧ r.y≠0#u32 ∧ r.lineX≠0#u32 ∧ r.lineY≠0#u32 ∧ r.lineZ≠0#u32 := by
  simpa [Port4C_GeometryGather.Row.words] using nonzero
 have oneEq : one=1#u32 := by
  change ok 1#u32=ok one at unit
  exact (Result.ok.inj unit).symm
 subst fibre; subst fleft; subst fright; subst one
 have small : ¬ (u >= 262144#usize) := by
  change ¬ (262144 ≤ u.val)
  omega
 refine ⟨Array.make 5#usize [r.x,r.y,r.lineX,r.lineY,r.lineZ],?_,?_⟩
 · simp only [NEO_GeometryScalarRef.gather,dictionary,cast,bind_tc_ok,if_neg small,pt]
   rw [div,bind_tc_ok]
   simp only [lift,←le,←re,lx,ly,mul,dbl,sub,bind_tc_ok]
   simp only [←rx,←ry,ne.1,ne.2.1,ne.2.2.1,ne.2.2.2.1,ne.2.2.2.2,if_false]
   rfl
 · simpa [Array.make,Port4C_GeometryGather.Row.words] using append

#print axioms accepted
end NEO_GeometryGather
end
