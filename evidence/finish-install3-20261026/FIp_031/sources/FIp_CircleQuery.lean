import FIp_CircleMade
import FIp_CircleAlgebra
import SAQ_LineArrays
import SAQ_QuerySource
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_CircleQuery
open Aeneas Aeneas.Std Result
open SAQ_WideABI

def toValues (a : Array E 4#usize) : Array W 4#usize :=
  ⟨a.val.map toW,by simpa using a.property⟩

def circle (alpha : E) (values : Array E 4#usize) (inverse : Array U32 5#usize) : Result E := do
  let z ← FIp_CircleSource.circle (toW alpha) (toValues values) inverse
  ok (fromW z)

theorem values (a b c d : E) :
    Port5Q1_OpeningValues.values (Array.make 4#usize [a,b,c,d]) =
      SAQ_LineSource.values4 (CheckpointBytes5Output.ofE a) (CheckpointBytes5Output.ofE b)
        (CheckpointBytes5Output.ofE c) (CheckpointBytes5Output.ofE d) := by
  funext j
  fin_cases j <;> rfl

theorem exact_circle (alpha : E) (v : Array E 4#usize) (inverse : Array U32 5#usize) (z : E)
    (run : circle alpha v inverse=ok z) :
    CheckpointBytes5Output.ofE z=FoldRuntimeAlgebra.circleWithInverses (CheckpointBytes5Output.ofE alpha)
      (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE
        (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 0)))
      (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE
        (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 1)))
      (Port5Q1_OpeningValues.values v) ∧ Port4C_QueryArithmetic.CanonE z := by
  obtain ⟨out,ho,he⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : fromW out=z := Result.ok.inj he
  subst z
  obtain ⟨a,b,c,d,hv⟩ := SAQ_LineArrays.four v
  obtain ⟨ix,iy,lx,ly,lz,hi⟩ := SAQ_LineArrays.five inverse
  subst v
  subst inverse
  have result := FIp_CircleMade.made (toW alpha) (toW a) (toW b) (toW c) (toW d)
    out ix iy lx ly lz ho
  have eq := result.2.trans (FIp_CircleAlgebra.formula _ _ _ _ _ _ _)
  have lane0 : Port5Q1_GeometryBinding.lane (Array.make 5#usize [ix,iy,lx,ly,lz]) 0=ix := rfl
  have lane1 : Port5Q1_GeometryBinding.lane (Array.make 5#usize [ix,iy,lx,ly,lz]) 1=iy := rfl
  constructor
  · rw [lane0,lane1,values]
    with_reducible simpa only [w_decode,toW,fromW,toQ,fromQ,Port5Q1_GeometryBinding.lane,
      Array.make,Fin.val_natCast,Nat.reduceMod,S7JoinBasisMachine.decode,SAQ_LineSource.decodeBase,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] using eq
  · exact (w_canonical (fromW out)).mpr result.1


#print axioms values
#print axioms exact_circle
end AspisR1.FIp_CircleQuery
end
