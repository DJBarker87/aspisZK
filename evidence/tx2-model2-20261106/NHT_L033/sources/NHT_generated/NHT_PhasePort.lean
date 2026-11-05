import VTop_Model
set_option autoImplicit false
namespace NHT_PhasePort
open Aeneas Aeneas.Std Result
abbrev Stage := AspisR1Stage2.verifier.Phase
abbrev Top := VTop_Stages.verifier.Phase

def toTop : Stage → Top
 | .Parsed => .Parsed | .Semantic => .Semantic | .SemanticPart n => .SemanticPart n
 | .Prepare => .Prepare | .CheckpointRead => .CheckpointRead | .Merkle n => .Merkle n
 | .Query n => .Query n | .QueryPart n k => .QueryPart n k
 | .CheckpointWrite => .CheckpointWrite | .Relation => .Relation | .Final => .Final

def toStage : Top → Stage
 | .Parsed => .Parsed | .Semantic => .Semantic | .SemanticPart n => .SemanticPart n
 | .Prepare => .Prepare | .CheckpointRead => .CheckpointRead | .Merkle n => .Merkle n
 | .Query n => .Query n | .QueryPart n k => .QueryPart n k
 | .CheckpointWrite => .CheckpointWrite | .Relation => .Relation | .Final => .Final

def observer (obs : Option (Top → Result Unit)) : Option (Stage → Result Unit) :=
 obs.map (fun f phase => f (toTop phase))

theorem roundtrip (p : Stage) : toStage (toTop p)=p := by cases p <;> rfl

theorem back (p : Top) : toTop (toStage p)=p := by cases p <;> rfl

theorem injective : Function.Injective toTop := by
 intro x y h
 have same := congrArg toStage h
 simpa only [roundtrip] using same

theorem release : observer none=none := rfl

theorem callback (f : Top → Result Unit) (p : Stage) :
 observer (some f)=some (fun p => f (toTop p)) := rfl
#print axioms roundtrip
#print axioms back
#print axioms injective
#print axioms release
#print axioms callback
end NHT_PhasePort
