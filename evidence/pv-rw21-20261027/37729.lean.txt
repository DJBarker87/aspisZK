import R1Z.ProverRw21PayloadTranscript
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21ProtocolRun
open R0P R0Z R0Z.HonestView R0Z.MaskLayout R1Z.Batched
open ProverRw21ProtocolOutput ProverCommitValueRange47
variable {F : Subfield Q}

/-- The honest mathematical protocol supplies all scalar payload coordinates.
The remaining digests/openings/node results are mathematical commitment data;
none is obtained by executing or projecting the deployed prover. -/
def transcript (pi : Fin 1024 ≃ Fin 1024) (pub : Public Q) (B : PackBasis F)
    (t : Trace Q) (ch : Challenges Q) (r : AffTape Q F)
    (root1 root2 foldedRoot : Digest) (openings : Fin 22 → Opening)
    (nodes : Fin 6 → Except ProverCommitPublish43.Error ProverCommitPublish43.Bytes) : Transcript :=
  ProverRw21PayloadTranscript.transcript (run (Bat := R1Bat) pi pub B t ch r)
    root1 root2 foldedRoot openings nodes

def output (pi : Fin 1024 ≃ Fin 1024) (pub : Public Q) (B : PackBasis F)
    (t : Trace Q) (ch : Challenges Q) (r : AffTape Q F)
    (root1 root2 foldedRoot : Digest) (openings : Fin 22 → Opening)
    (nodes : Fin 6 → Except ProverCommitPublish43.Error ProverCommitPublish43.Bytes) :=
  ProverRw21ModelInstance (.ok (.Ok (transcript pi pub B t ch r
    root1 root2 foldedRoot openings nodes)))

#print axioms transcript
#print axioms output
end R1Z.ProverRw21ProtocolRun
