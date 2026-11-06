import NJC_ReaderResults
import Port5Q2_ReaderWeights
set_option autoImplicit false
noncomputable section
namespace NJC_Sections
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- The complete native window specification, with the actual emitted raw read
at the SAME Reader pre-state. No arbitrary successful decode or backing. -/
def readK (r : verifier.Reader) := do
 let (b,out) ← CheckpointBytes3Reader.raw 16#usize r
 ok (NJC_ReaderResults.naturalK b,out)

theorem child (r : verifier.Reader) : readK r=CheckpointBytes3Reader.readK r :=
 (NJC_ReaderResults.k r).symm

/-- The frozen semantic helper has ten explicit call occurrences. Install the
complete K law in its emitted sequencing, retaining every rejection prefix. -/
theorem semantic (bytes : Slice U8) (start : Usize) :
 CheckpointBytes4Ops.semanticUsing readK bytes start=
 CheckpointBytes4Ops.readSemanticAlpha bytes start := by
 have same : readK=CheckpointBytes3Reader.readK := funext child
 rw [same]
 rfl

/-- The actual mutable-weight sequencing consumes the same complete K law.
The source weight loop is covered by one arbitrary native iteration; its
induction and deferred backwrites are the retained emitted helper below. -/
theorem weights (bytes : Slice U8) (start : Usize)
 (values : alloc.vec.Vec aspis_core.field.QM31) :
 CheckpointBytes4Ops.weightsUsing readK bytes start values=
 CheckpointBytes4Ops.readWeights bytes start values := by
 have same : readK=CheckpointBytes3Reader.readK := funext child
 rw [same]
 rfl

/-- Parametric loop induction is inherited without whole-buffer native unwind.
No allocator-success, output-success or child-Result hypothesis. -/
theorem induction (n : Nat) (reader : verifier.Reader)
 (iter : core.slice.iter.IterMut aspis_core.field.QM31) :
 CheckpointBytes4Sections.weightLoop readK n reader iter=
 CheckpointBytes4Sections.weightLoop CheckpointBytes3Reader.readK n reader iter := by
 have same : readK=CheckpointBytes3Reader.readK := funext child
 rw [same]

#print axioms child
#print axioms semantic
#print axioms weights
#print axioms induction
end NJC_Sections
