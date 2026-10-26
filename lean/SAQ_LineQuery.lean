import SAQ_LineJoin
import SAQ_LineArrays
import SAQ_QuerySource
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_LineQuery
open Aeneas Aeneas.Std Result
open SAQ_WideABI

def toValues (a : Array E 4#usize) : Array W 4#usize :=
  ⟨a.val.map toW,by simpa using a.property⟩

def line (alpha : E) (values : Array E 4#usize) (inverse : Array U32 5#usize) : Result E := do
  let z ← SAQ_LineSource.line (toW alpha) (toValues values) inverse
  ok (fromW z)

theorem values (a b c d : E) :
    Port5Q1_OpeningValues.values (Array.make 4#usize [a,b,c,d]) =
      SAQ_LineSource.values4 (CheckpointBytes5Output.ofE a) (CheckpointBytes5Output.ofE b)
        (CheckpointBytes5Output.ofE c) (CheckpointBytes5Output.ofE d) := by
  funext j
  fin_cases j <;> rfl

theorem exact_line (alpha : E) (v : Array E 4#usize) (inverse : Array U32 5#usize) (z : E)
    (run : line alpha v inverse=ok z) :
    CheckpointBytes5Output.ofE z=FoldRuntimeAlgebra.lineWithInverses (CheckpointBytes5Output.ofE alpha)
      (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE
        (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 2)))
      (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE
        (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 3)))
      (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE
        (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 4)))
      (Port5Q1_OpeningValues.values v) ∧ Port4C_QueryArithmetic.CanonE z := by
  obtain ⟨out,ho,he⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : fromW out=z := Result.ok.inj he
  subst z
  obtain ⟨a,b,c,d,hv⟩ := SAQ_LineArrays.four v
  obtain ⟨ix,iy,lx,ly,lz,hi⟩ := SAQ_LineArrays.five inverse
  subst v
  subst inverse
  obtain ⟨cut⟩ := SAQ_LineSource.cuts (toW alpha) (toW a) (toW b) (toW c) (toW d)
    out ix iy lx ly lz ho
  have result := SAQ_LineJoin.on_cuts (toW alpha) (toW a) (toW b) (toW c) (toW d)
    out lx ly lz cut
  have eq := result.2.trans (SAQ_LineArrays.source_eq_inverses _ _ _ _ _)
  have lane2 : Port5Q1_GeometryBinding.lane (Array.make 5#usize [ix,iy,lx,ly,lz]) 2=lx := rfl
  have lane3 : Port5Q1_GeometryBinding.lane (Array.make 5#usize [ix,iy,lx,ly,lz]) 3=ly := rfl
  have lane4 : Port5Q1_GeometryBinding.lane (Array.make 5#usize [ix,iy,lx,ly,lz]) 4=lz := rfl
  constructor
  · rw [lane2,lane3,lane4,values]
    with_reducible simpa only [w_decode,toW,fromW,toQ,fromQ,Port5Q1_GeometryBinding.lane,
      Array.make,Fin.val_natCast,Nat.reduceMod,S7JoinBasisMachine.decode,SAQ_LineSource.decodeBase,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] using eq
  · exact (w_canonical (fromW out)).mpr result.1

def install (ops : SAQ_Query.Ops) : SAQ_Query.Ops :=
  {SAQ_QuerySource.install ops with op16 := line}

structure Remaining (ops : SAQ_Query.Ops) : Prop where
  decoder : Port5Q1_OpeningValues.SessionAS3 ops

theorem primitives (ops : SAQ_Query.Ops) (rest : Remaining (install ops)) :
    Port5Q1_QueryPorts.SessionAPrimitives (install ops) := by
  refine ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,?_,?_,rest.decoder,?_,?_⟩
  · exact ⟨SAQ_MixedSource.mulE_exact,SAQ_Arithmetic.add_exact,SAQ_Arithmetic.mulK_exact⟩
  · exact ⟨(SAQ_Query.m31 ops).multiply,(SAQ_Query.m31 ops).double,
      (SAQ_Query.m31 ops).one,(SAQ_Query.m31 ops).subtract⟩
  · intro alpha values inverse z run
    exact (exact_line alpha values inverse z run).1
  · intro alpha values inverse z run
    exact (exact_line alpha values inverse z run).2

#print axioms values
#print axioms exact_line
#print axioms primitives
end AspisR1.SAQ_LineQuery
end
