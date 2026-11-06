import NLN_BatchPacket
import NLN_TX2_054
set_option autoImplicit false
noncomputable section
namespace NLN_TX2_053
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem root (H : Bytes → State) (proof : Slice U8) (len : proof.val.length=57607)
 (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=MultiproofConeCanonical.bytesOf proof.val)
 (p : verifier.Prepared) (folded : NLL.Root)
 (canonical : ∀ j,j<22 → p.queries.val[j]!.val<262144)
 (rootValues : ∀ k : Fin 3, Port3_NativeBatchCalls.rootAt (NLL_BatchSource.roots p folded) k=
   encodeState (OraclePortBatchDraft.committedRoot parsed k.val)) :
 NLN.BatchPacket H proof parsed p folded 1#usize :=
 NLN.batch H proof parsed p folded 1#usize
   (NLN_TX2_054.root H proof len parsed wire p.queries (NLL_BatchSource.roots p folded) canonical rootValues)

set_option pp.proofs false
#print root
#print axioms root
end NLN_TX2_053
end
