-- PCVN_ item (1) op13: the deployed marker slot (NHV_ReleaseOps.mark) equals the fresh 4bb3b3f emission of verifier::mark
-- (text of PCQC_E011 / PRVFresh_CurrentCompactCallerModelV1, overflow-checks ON) behind the nominal Phase ports.
import Aeneas
import CurrentCompactCallerModelV1
import NHV_ReleaseOps
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace AspisR1CurrentCaller
namespace PCVN_FreshMark
/-- [aspis_r1_cost_probe::verifier::mark] fresh text, copied from the 4bb3b3f emission. -/
def verifier.mark
  (obs : Option (verifier.Phase → Result Unit)) (p : verifier.Phase) :
  Result Unit
  := do
  match obs with
  | none => ok ()
  | some f => f p
end PCVN_FreshMark
end AspisR1CurrentCaller

namespace PCVN_Op13
open AspisR1CurrentCaller

abbrev VP := VTop_Stages.verifier.Phase
abbrev CP := AspisR1CurrentCaller.verifier.Phase

def toC : VP → CP
  | .Parsed => .Parsed | .Semantic => .Semantic | .SemanticPart a => .SemanticPart a | .Prepare => .Prepare
  | .CheckpointRead => .CheckpointRead | .Merkle n => .Merkle n | .Query n => .Query n
  | .QueryPart n a => .QueryPart n a | .CheckpointWrite => .CheckpointWrite | .Relation => .Relation | .Final => .Final
def fromC : CP → VP
  | .Parsed => .Parsed | .Semantic => .Semantic | .SemanticPart a => .SemanticPart a | .Prepare => .Prepare
  | .CheckpointRead => .CheckpointRead | .Merkle n => .Merkle n | .Query n => .Query n
  | .QueryPart n a => .QueryPart n a | .CheckpointWrite => .CheckpointWrite | .Relation => .Relation | .Final => .Final

theorem fromC_toC (p : VP) : fromC (toC p) = p := by cases p <;> rfl

/-- fresh = gate (same text as the gate constant). -/
theorem fresh_eq_gate : @PCVN_FreshMark.verifier.mark = @AspisR1CurrentCaller.verifier.mark := rfl

theorem op13_frozen (obs : Option (VP → Result Unit)) (p : VP) :
    NHV_ReleaseOps.mark obs p =
      PCVN_FreshMark.verifier.mark (Option.map (fun f q => f (fromC q)) obs) (toC p) := by
  cases obs with
  | none => rfl
  | some f => simp only [NHV_ReleaseOps.mark, PCVN_FreshMark.verifier.mark, Option.map, fromC_toC]

#print axioms fromC_toC
#print axioms fresh_eq_gate
#print axioms op13_frozen
end PCVN_Op13
