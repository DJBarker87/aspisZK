import NLN_ValuesPacket
import NLN_TX1_083
set_option autoImplicit false
noncomputable section
namespace NLN_TX1_082
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem root (H : Bytes → State) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (raw : Array U32 22#usize) (roots : Roots)
 (canonical : ∀ j,j<22 → raw.val[j]!.val<262144)
 (rootValues : ∀ k : Fin 3, Port3_NativeBatchCalls.rootAt roots k=
   encodeState (OraclePortBatchDraft.committedRoot p k.val)) :
 NLN.ValuesPacket H proof p raw roots 0#usize := by
 apply NLN.values
 intro c member
 exact NLN_TX1_083.root H proof len p wire raw c.1 c.2
   (NLL_ValuesReturning.kinds roots c member) canonical (NLN.bindings p roots rootValues c member)

set_option pp.proofs false
#print root
#print axioms root
end NLN_TX1_082
end
