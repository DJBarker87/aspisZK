import NNC_WriterHeader
import RPz7_DrvC_AcceptedCalls
set_option autoImplicit false
noncomputable section
namespace NNC_FirstWriter
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical DrvC_Installation
/-- Construct the writer run from TX1 alone. No second cut or accepted2
premise occurs; the installed dictionary equality is proved internally. -/
theorem reached {F C : Type} (c : Configuration F C)
 (semantic : Port1_Driver.Semantic) (pub proof : Slice U8)
 (split : Usize) (saved : alloc.vec.Vec U8)
 (accepted : AdapterRw.first_decoded (sdk c) semantic pub proof split=ok (.Ok saved)) :
 Nonempty (Tx1Q_Execution.Run
  (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std)
  c.reserved c.query c.geometry (currentDigest c) ()
  (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split saved) := by
 have tx := DrvC_AcceptedCalls.current_success c semantic pub proof split saved accepted
 have same : currentInstalled c =
  Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std := by
  unfold currentInstalled current
  rw [Uni_Install.compose_tx1]
  rfl
 rw [same] at tx
 exact Tx1Q_Execution.accepted_generic _ c.reserved c.query c.geometry (currentDigest c) ()
  (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split saved
  (Tx1Q_Execution.actual_slots _ c.reserved c.query c.geometry c.boundaries c.std) tx

/-- Both writer facts used by NMF', from TX1's own accepted call only.
The oracle is the existing per-call returning-value runtime interpretation. -/
theorem facts {F C : Type} (c : Configuration F C)
 (semantic : Port1_Driver.Semantic) (pub proof : Slice U8)
 (split : Usize) (saved : alloc.vec.Vec U8)
 (H : Bytes → State)
 (oracle : CheckpointBytes5Inputs.Oracle
  (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))) () H)
 (accepted : AdapterRw.first_decoded (sdk c) semantic pub proof split=ok (.Ok saved)) :
 NLP_InputDomain.Root0 saved.deref proof ∧
 NLW_ReaderHeader.decode (bytesOf saved.val)=some (H (bytesOf proof.val),H (bytesOf pub.val)) := by
 obtain ⟨run⟩ := reached c semantic pub proof split saved accepted
 have preparedRoot := NMF_WriterRoots.physical _ _ _ _ _ _ _ () _ pub proof split saved run
 constructor
 · exact NMF_WriterRoots.serialized _ () _ _ proof pub saved run.writer_call preparedRoot
 · exact NNC_WriterHeader.returned _ _ _ proof pub () saved H oracle run.writer_call
#print axioms reached
#print axioms facts
end NNC_FirstWriter
