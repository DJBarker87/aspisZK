import NMT_Transport_T9
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMT_Transport
open Aeneas Aeneas.Std
def toT10 : NMT_tx1.verifier.Error → AspisR1CurrentCaller.verifier.Error
 | .Parse => .Parse
 | .Semantic => .Semantic
 | .Transcript => .Transcript
 | .Relation => .Relation
 | .Merkle => .Merkle
 | .Query => .Query
 | .Checkpoint => .Checkpoint
 | .Allocation => .Allocation
def fromT10 : AspisR1CurrentCaller.verifier.Error → NMT_tx1.verifier.Error
 | .Parse => .Parse
 | .Semantic => .Semantic
 | .Transcript => .Transcript
 | .Relation => .Relation
 | .Merkle => .Merkle
 | .Query => .Query
 | .Checkpoint => .Checkpoint
 | .Allocation => .Allocation
@[simp] theorem toT10_inverse (x : NMT_tx1.verifier.Error) : fromT10 (toT10 x)=x := by
 cases x <;> simp [toT10,fromT10]
#print axioms toT10_inverse
@[simp] theorem fromT10_inverse (x : AspisR1CurrentCaller.verifier.Error) : toT10 (fromT10 x)=x := by
 cases x <;> simp [fromT10,toT10]
#print axioms fromT10_inverse
end AspisR1.NMT_Transport
