import NMT_Transport_T15
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMT_Transport
open Aeneas Aeneas.Std
def toT16 : NMT_tx1.verifier.Phase → AspisR1CurrentCaller.verifier.Phase
 | .Parsed => .Parsed
 | .Semantic => .Semantic
 | .SemanticPart x0 => .SemanticPart (x0)
 | .Prepare => .Prepare
 | .CheckpointRead => .CheckpointRead
 | .Merkle x0 => .Merkle (x0)
 | .Query x0 => .Query (x0)
 | .QueryPart x0 x1 => .QueryPart (x0) (x1)
 | .CheckpointWrite => .CheckpointWrite
 | .Relation => .Relation
 | .Final => .Final
def fromT16 : AspisR1CurrentCaller.verifier.Phase → NMT_tx1.verifier.Phase
 | .Parsed => .Parsed
 | .Semantic => .Semantic
 | .SemanticPart x0 => .SemanticPart (x0)
 | .Prepare => .Prepare
 | .CheckpointRead => .CheckpointRead
 | .Merkle x0 => .Merkle (x0)
 | .Query x0 => .Query (x0)
 | .QueryPart x0 x1 => .QueryPart (x0) (x1)
 | .CheckpointWrite => .CheckpointWrite
 | .Relation => .Relation
 | .Final => .Final
@[simp] theorem toT16_inverse (x : NMT_tx1.verifier.Phase) : fromT16 (toT16 x)=x := by
 cases x <;> simp [toT16,fromT16]
#print axioms toT16_inverse
@[simp] theorem fromT16_inverse (x : AspisR1CurrentCaller.verifier.Phase) : toT16 (fromT16 x)=x := by
 cases x <;> simp [fromT16,toT16]
#print axioms fromT16_inverse
end AspisR1.NMT_Transport
