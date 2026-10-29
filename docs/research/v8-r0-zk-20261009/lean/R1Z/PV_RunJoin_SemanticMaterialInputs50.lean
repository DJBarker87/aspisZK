import R1Z.PV_RunJoin_SemanticArray50
import R1Z.PV_RunJoin_SemanticPoints50
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SemanticMaterialInputs50
open Aeneas Aeneas.Std ProverRwFull
open ProverCommitPrimitive47
abbrev Sem := host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn

def alpha (s : Sem) : Nat → Old.Q := PV_RunJoin_SemanticArray50.raw 10#usize s.alpha
def x0 (s : Sem) : Old.Q := PV_RunJoin_SemanticScalar50.raw (PV_RunJoin_SemanticPoints50.read s.z 0).x
def y0 (s : Sem) : Old.Q := PV_RunJoin_SemanticScalar50.raw (PV_RunJoin_SemanticPoints50.read s.z 0).y
def x1 (s : Sem) : Old.Q := PV_RunJoin_SemanticScalar50.raw (PV_RunJoin_SemanticPoints50.read s.z 1).x
def y1 (s : Sem) : Old.Q := PV_RunJoin_SemanticScalar50.raw (PV_RunJoin_SemanticPoints50.read s.z 1).y

theorem alpha_eq (s : Sem) : PV_RunJoin_MaterialInputs49.alpha (alpha s)=s.alpha :=
  PV_RunJoin_SemanticArray50.complete _ _
theorem points_eq (s : Sem) : PV_RunJoin_MaterialInputs49.points (x0 s) (y0 s) (x1 s) (y1 s)=s.z :=
  PV_RunJoin_SemanticPoints50.complete _
#print axioms alpha
#print axioms x0
#print axioms y0
#print axioms x1
#print axioms y1
#print axioms alpha_eq
#print axioms points_eq
end R1Z.PV_RunJoin_SemanticMaterialInputs50
