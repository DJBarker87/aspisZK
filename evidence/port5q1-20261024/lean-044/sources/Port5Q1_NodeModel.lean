import Port5Q1_Advance
import Port5Q1_Domain
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_NodeModel
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody
open AspisCircleGroupOrder
abbrev FP := ZMod P
abbrev FK := OraclePortCheckpointAbiC5.K

structure SessionAM31 (ops : Ops) : Prop where
  multiply : ∀ x y z, ops.op7 x y=ok z →
    S7JoinBasisMachine.decode z=S7JoinBasisMachine.decode x*S7JoinBasisMachine.decode y
  double : ∀ x y, ops.op8 x=ok y → S7JoinBasisMachine.decode y=2*S7JoinBasisMachine.decode x
  one : ∀ x, ops.op5=ok x → S7JoinBasisMachine.decode x=1
  subtract : ∀ x y z, ops.op6 x y=ok z →
    S7JoinBasisMachine.decode z=S7JoinBasisMachine.decode x-S7JoinBasisMachine.decode y

theorem node (ops : Ops) (leaves : SessionAM31 ops) (u : Fin 65536)
    (z square doubled one out : U32)
    (line : S7JoinBasisMachine.decode z=FoldGeometryBridge.lz u)
    (mul : ops.op7 z z=ok square) (dbl : ops.op8 square=ok doubled)
    (unit : ops.op5=ok one) (sub : ops.op6 doubled one=ok out) :
    S7JoinBasisMachine.decode out=AspisV5FriReleasedLineGeometry.storedLine16X u := by
  rw [leaves.subtract _ _ _ sub,leaves.double _ _ dbl,leaves.multiply _ _ _ mul,
    leaves.one _ unit,line]
  have model := S7OwnedP6StoredNode.extra_t2_is_final_node (K:=FP) u
  simpa only [pow_two,algebraMap_self] using model

theorem scalar_map (x : FP) : Port4C_SumField.scalar x=algebraMap FP FK x := by
  rfl

theorem basis (q : Fin 22 → Fin 262144) (j : Fin 22) (out : U32)
    (meaning : S7JoinBasisMachine.decode out=
      AspisV5FriReleasedLineGeometry.storedLine16X (AspisR1.parentIndex (n:=65536) (q j))) (i : Fin 64) :
    Port4C_SumField.scalar (AspisCircleTensorBinding.naturalLineValue
      (S7JoinBasisMachine.decode out) i.val)=QueryResidualBridge.basis (K:=FK) q j i := by
  rw [meaning,scalar_map,NaturalEmbedding.map_naturalLineValue]
  rfl

#print axioms node
#print axioms scalar_map
#print axioms basis
end AspisR1.Port5Q1_NodeModel
end
