import Port5Q1_Geometry
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_Domain
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeGeometryBody
open AspisCircleGroupOrder AspisCircleTensorBinding
abbrev FP := ZMod P
variable {CoreError : Type}

def index (u : Nat) : Fin 262144 := ⟨u%262144,Nat.mod_lt _ (by decide)⟩
def parent (u : Nat) : Fin 65536 := ⟨u/4%65536,Nat.mod_lt _ (by decide)⟩
def lineZ (u : Nat) : FP := FoldGeometryBridge.lz (parent u)
def words (u : Nat) : List FP :=
  [X (FoldStoredGeometry.sourceFibre (index u)),(FoldStoredGeometry.sourceFibre (index u)).1.2,
    FoldGeometryBridge.lx (parent u),FoldGeometryBridge.ly (parent u),lineZ u]

/-- Session A's fast-domain and base-field primitive interpretations, indexed
only by each primitive's actual operands/return. No geometry success is hidden. -/
structure SessionADomain (ops : Ops CoreError) : Prop where
  fibre : ∀ u f, ops.op12 u=ok (.Ok f) → f=u ∧ f.val<262144
  point : ∀ f p, ops.op15 f=ok p →
    S7JoinBasisMachine.decode p.x=X (FoldStoredGeometry.sourceFibre (index f.val)) ∧
    S7JoinBasisMachine.decode p.y=(FoldStoredGeometry.sourceFibre (index f.val)).1.2
  line : ∀ f x, ops.op14 f=ok x →
    S7JoinBasisMachine.decode x=FoldStoredGeometry.sourceX18 (index f.val)
  multiply : ∀ x y z, ops.op9 x y=ok z →
    S7JoinBasisMachine.decode z=S7JoinBasisMachine.decode x*S7JoinBasisMachine.decode y
  double : ∀ x y, ops.op10 x=ok y → S7JoinBasisMachine.decode y=2*S7JoinBasisMachine.decode x
  one : ∀ x, ops.op7=ok x → S7JoinBasisMachine.decode x=1
  subtract : ∀ x y z, ops.op8 x y=ok z →
    S7JoinBasisMachine.decode z=S7JoinBasisMachine.decode x-S7JoinBasisMachine.decode y

theorem gathered_row (ops : Ops CoreError) (leaves : SessionADomain ops) (start : Usize)
    (iter iter1 iterOut : core.slice.iter.Iter U32) (query : U32)
    (zs zsOut flat flatOut : alloc.vec.Vec U32)
    (next : core.slice.iter.IteratorSliceIter.next iter=ok (some query,iter1))
    (run : verifier.QueryGeometry.for_range_loop0.body (Port4C_GeometryStd.install ops)
      start iter zs flat=ok (cont (iterOut,zsOut,flatOut))) :
    query.val<262144 ∧
    flatOut.val.map S7JoinBasisMachine.decode=flat.val.map S7JoinBasisMachine.decode++words query.val ∧
    zsOut.val.map S7JoinBasisMachine.decode=zs.val.map S7JoinBasisMachine.decode++[lineZ query.val] := by
  obtain ⟨r,u,v,left,right,fibre,fleft,fright,point,square,doubled,one,fields⟩ :=
    Port4C_GeometryGather.step ops start iter iter1 iterOut query zs zsOut flat flatOut next run
  rcases fields with ⟨_,cast,new,pointRun,div,leftEq,newLeft,lineX,rightEq,newRight,lineY,hx,hy,mul,dbl,unit,sub,_,append,line⟩
  have fi := leaves.fibre _ _ new
  have fl := leaves.fibre _ _ newLeft
  have fr := leaves.fibre _ _ newRight
  have castEq : u=UScalar.cast .Usize query := (Result.ok.inj cast).symm
  have uv : u.val=query.val := by
    rw [castEq,UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    have limit : query.val<4294967296 := query.bv.isLt
    have cap : 4294967296 < 2^UScalarTy.Usize.numBits := by change 4294967296 < 2^64; norm_num
    exact Nat.lt_trans limit cap
  have vb : v.val=u.val/4 := by
    obtain ⟨out,hout,value⟩ := UScalar.div_spec u (y:=4#usize) (by decide)
    have same := Result.ok.inj (hout.symm.trans div)
    subst out
    exact value
  have cap : 262144 < 2^UScalarTy.Usize.numBits := by change 262144 < 2^64; norm_num
  have ub : u.val<262144 := by rw [←fi.1]; exact fi.2
  have lv : left.val=v.val*4 := by
    rw [leftEq]
    rw [Usize.wrapping_mul_val_eq]
    apply Nat.mod_eq_of_lt
    change v.val*4 < 2^UScalarTy.Usize.numBits
    rw [vb]; omega
  have rv : right.val=left.val+3 := by
    rw [rightEq]
    rw [Usize.wrapping_add_val_eq]
    apply Nat.mod_eq_of_lt
    change left.val+3 < 2^UScalarTy.Usize.numBits
    rw [lv,vb]; omega
  have bound : query.val<262144 := by rw [←uv,←fi.1]; exact fi.2
  have p0 : index fleft.val=AspisR1.childIndex (parent query.val) 0 := by
    apply Fin.ext
    dsimp only [index,parent,AspisR1.childIndex]
    rw [fl.1,lv,vb,uv,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]
    omega
  have p3 : index fright.val=AspisR1.childIndex (parent query.val) 3 := by
    apply Fin.ext
    dsimp only [index,parent,AspisR1.childIndex]
    rw [fr.1,rv,lv,vb,uv,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]
    omega
  have cp := leaves.point _ _ pointRun
  have cx : S7JoinBasisMachine.decode r.lineX=FoldGeometryBridge.lx (parent query.val) := by
    rw [leaves.line _ _ lineX,p0]
    rfl
  have cy : S7JoinBasisMachine.decode r.lineY=FoldGeometryBridge.ly (parent query.val) := by
    rw [leaves.line _ _ lineY,p3]
    rfl
  have cz : S7JoinBasisMachine.decode r.lineZ=lineZ query.val := by
    rw [leaves.subtract _ _ _ sub,leaves.double _ _ dbl,leaves.multiply _ _ _ mul,
      leaves.one _ unit,cx]
    unfold lineZ FoldGeometryBridge.lz
    rw [pow_two]
  have pointIndex : index fibre.val=index query.val := by rw [fi.1,uv]
  have row : r.words.map S7JoinBasisMachine.decode=words query.val := by
    change [S7JoinBasisMachine.decode r.x,S7JoinBasisMachine.decode r.y,
      S7JoinBasisMachine.decode r.lineX,S7JoinBasisMachine.decode r.lineY,
      S7JoinBasisMachine.decode r.lineZ]=_
    rw [hx,hy,cp.1,cp.2,pointIndex,cx,cy,cz]
    rfl
  refine ⟨bound,?_,?_⟩
  · rw [append,List.map_append,row]
  · rw [line,List.map_append,List.map_cons,List.map_nil,cz]

#print axioms gathered_row
end AspisR1.Port5Q1_Domain
end
