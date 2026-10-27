import R1Z.ProverRw21ModelInstance
import R1Z.PhaseMessageDependenciesBin
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21PayloadTranscript
open R0P R0Z R0Z.HonestView R0Z.MaskLayout R1Z.Batched
open ProverRw21ProtocolOutput ProverCommitValueRange47

def semantic (p : Payload Q R1Bat) (root1 root2 : Digest) : Semantic where
  root1 := root1
  root2 := root2
  mask := p .maskSum
  rounds := fun r c => p (.semanticCoeff r c)
  claims := fun i => if h : i.val<87 then
    p (.pointClaim ⟨i.val/29,by omega⟩ ⟨i.val%29,by omega⟩)
    else p (.extraClaim ⟨i.val-87,by have := i.isLt; omega⟩)
  endpoint := fun c => p (.ood 0 c)

def transcript (p : Payload Q R1Bat) (root1 root2 foldedRoot : Digest)
    (openings : Fin 22 → Opening)
    (nodes : Fin 6 → Except ProverCommitPublish43.Error ProverCommitPublish43.Bytes) : Transcript where
  semantic := semantic p root1 root2
  y1 := fun c => p (.ood 1 c)
  inactive := embed (p .inactiveSum)
  round0 := fun c => embed (p (.bat (.round0 c)))
  foldedRoot := foldedRoot
  round1 := fun c => embed (p (.bat (.round1 c)))
  finalValues := fun c => embed (p (.bat (.final c)))
  openings := openings
  nodes := nodes

/-- Mathematical protocol payload to mathematical byte output. Caller decoding,
mask/oracle scheduling, opening construction, and source correspondence remain
separate obligations; no source result occurs in this definition. -/
def output (p : Payload Q R1Bat) (root1 root2 foldedRoot : Digest)
    (openings : Fin 22 → Opening)
    (nodes : Fin 6 → Except ProverCommitPublish43.Error ProverCommitPublish43.Bytes) :=
  ProverRw21ModelInstance (.ok (.Ok (transcript p root1 root2 foldedRoot openings nodes)))

#print axioms semantic
#print axioms transcript
#print axioms output
end R1Z.ProverRw21PayloadTranscript
