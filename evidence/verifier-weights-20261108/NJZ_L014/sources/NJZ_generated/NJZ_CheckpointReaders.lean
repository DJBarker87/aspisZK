import NJZ_Readers
import Port5Q2_ReaderSemantic
import Port5Q2_ReaderWeights
import T2Nat_WeightSequence
import NJR_WeightFailure
set_option autoImplicit false
noncomputable section
namespace NJZ_CheckpointReaders
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 NIL_Carriers

/-- The concrete emitted Reader installed at the old nominal carrier. -/
def readK (r : verifier.Reader) := outer
 (fun x=>(inner NIL_Carriers.k x.1,reader x.2)) (NJZ_Readers.k (unReader r))

theorem scalar (r : verifier.Reader) : readK r=CheckpointBytes3Reader.readK r := by
 unfold readK
 rw [NJZ_Readers.k_reference,NIL_FreshOps.k_port,reader_reverse]

/-- Exact ten explicit source calls; all error and abort prefixes retained. -/
theorem semantic (bytes : Slice U8) (at : Usize) :
 Port5Q2_ReaderSemantic.semantic readK bytes at=
 CheckpointBytes4Ops.readSemanticAlpha bytes at := by
 have same : readK=CheckpointBytes3Reader.readK := funext scalar
 rw [same,Port5Q2_ReaderSemantic.normalization]
 rfl

/-- Exact source iterator/body/writeback chain, consuming the concrete Reader
law, not an assumed helper result or an arbitrary dictionary. -/
theorem weights (bytes : Slice U8) (at : Usize)
 (before : alloc.vec.Vec aspis_core.field.QM31) :
 Port5Q2_ReaderWeights.weights readK bytes at before=
 CheckpointBytes4Ops.readWeights bytes at before := by
 have same : readK=CheckpointBytes3Reader.readK := funext scalar
 rw [same]
 exact T2Nat_WeightSequence.weights bytes at before

#print axioms scalar
#print axioms semantic
#print axioms weights
end NJZ_CheckpointReaders
