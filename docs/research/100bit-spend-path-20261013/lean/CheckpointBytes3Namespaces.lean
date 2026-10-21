import OraclePortCkptAbiSourceFields
import CheckpointBytesDecodeC5

set_option autoImplicit false
namespace AspisR1.CheckpointBytes3Namespaces
open Aeneas Aeneas.Std

def toK (x : AspisR1Stage2.aspis_core.field.QM31) : OraclePortCkptAbi2Extracted.aspis_core.field.QM31 :=
  ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def fromK (x : OraclePortCkptAbi2Extracted.aspis_core.field.QM31) : AspisR1Stage2.aspis_core.field.QM31 :=
  ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def toE (x : AspisR1Stage2.aspis_core.field.wide_exact.WideExact) : OraclePortCkptAbi2Extracted.aspis_core.field.wide_exact.WideExact :=
  ⟨toK x.c0,toK x.c1⟩
def fromE (x : OraclePortCkptAbi2Extracted.aspis_core.field.wide_exact.WideExact) : AspisR1Stage2.aspis_core.field.wide_exact.WideExact :=
  ⟨fromK x.c0,fromK x.c1⟩
def toPoint (x : AspisR1Stage2.aspis_core.circle.SecureCirclePoint) : OraclePortCkptAbi2Extracted.aspis_core.circle.SecureCirclePoint :=
  ⟨toK x.x,toK x.y⟩
def fromPoint (x : OraclePortCkptAbi2Extracted.aspis_core.circle.SecureCirclePoint) : AspisR1Stage2.aspis_core.circle.SecureCirclePoint :=
  ⟨fromK x.x,fromK x.y⟩
def toVariant : AspisR1Stage2.transport.Variant → OraclePortCkptAbi2Extracted.aspis_r1_cost_probe.transport.CheckpointAbi2Variant
  | .S1 => .S1 | .S2 => .S2 | .D => .D

def mapArray {A B : Type} {n : Usize} (f : A → B) (x : Array A n) : Array B n :=
  ⟨x.val.map f,by simpa using x.property⟩
def mapVec {A B : Type} (f : A → B) (x : alloc.vec.Vec A) : alloc.vec.Vec B :=
  ⟨x.val.map f,by simpa using x.property⟩

def toPrepared (p : AspisR1Stage2.verifier.Prepared) : OraclePortCkptAbi2Extracted.aspis_r1_cost_probe.verifier.Prepared where
  variant := toVariant p.variant
  roots := p.roots
  gamma := toE p.gamma
  kappa := toE p.kappa
  alpha := mapArray toE p.alpha
  rho := toK p.rho
  queries := p.queries
  semantic_alpha := mapArray toK p.semantic_alpha
  z := mapArray toPoint p.z
  claim := toE p.claim
  state := p.state

def toAccumulator (a : AspisR1Stage2.verifier.Accumulator) : OraclePortCkptAbi2Extracted.aspis_r1_cost_probe.verifier.Accumulator where
  weights := mapVec toK a.weights
  rhs := toE a.rhs
  power := toK a.power
  next := a.next

@[simp] theorem from_to_k (x : AspisR1Stage2.aspis_core.field.QM31) : fromK (toK x) = x := by
  cases x with | mk a b => cases a; cases b; rfl
@[simp] theorem to_from_k (x : OraclePortCkptAbi2Extracted.aspis_core.field.QM31) : toK (fromK x) = x := by
  cases x with | mk a b => cases a; cases b; rfl
@[simp] theorem from_to_e (x : AspisR1Stage2.aspis_core.field.wide_exact.WideExact) : fromE (toE x) = x := by
  cases x; simp [fromE,toE]
@[simp] theorem to_from_e (x : OraclePortCkptAbi2Extracted.aspis_core.field.wide_exact.WideExact) : toE (fromE x) = x := by
  cases x; simp [fromE,toE]

theorem prepared_fields (p : AspisR1Stage2.verifier.Prepared) :
    (toPrepared p).roots = p.roots ∧ (toPrepared p).state = p.state ∧
    (toPrepared p).queries = p.queries ∧
    (toPrepared p).semantic_alpha.val = p.semantic_alpha.val.map toK ∧
    (toPrepared p).alpha.val = p.alpha.val.map toE ∧
    (toPrepared p).z.val = p.z.val.map toPoint := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem accumulator_fields (a : AspisR1Stage2.verifier.Accumulator) :
    (toAccumulator a).weights.val = a.weights.val.map toK ∧
    (toAccumulator a).next = a.next ∧
    (toAccumulator a).rhs = toE a.rhs ∧ (toAccumulator a).power = toK a.power := ⟨rfl,rfl,rfl,rfl⟩

#print axioms from_to_k
#print axioms to_from_k
#print axioms from_to_e
#print axioms to_from_e
#print axioms prepared_fields
#print axioms accumulator_fields
#print Usize.max
#print UScalar.max
#print UScalar.or
end AspisR1.CheckpointBytes3Namespaces
