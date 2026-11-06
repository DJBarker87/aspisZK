import NLN_TX2_053
import NLB_NativeFold
set_option autoImplicit false
noncomputable section
namespace NLP_NativeMerkle
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Fixed explicit-Result native reference from the CLOSED child packet.
Digest realization uses the existing runtime H interpretation, not a new hash
assumption. No arbitrary Merkle dictionary is installed. -/
def action (H : Bytes → State) : NJU_CommonObserved.Merkle :=
 fun {X} _ proof p folded batch _ => NHT_ResultPort.action
  (NKV_FRef.verifier.candidate.batch_merkle (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof p folded batch ())
set_option pp.proofs false
#print action
end NLP_NativeMerkle
