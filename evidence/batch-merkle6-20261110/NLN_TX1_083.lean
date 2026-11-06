import NLN_TreePacket
set_option autoImplicit false
noncomputable section
namespace NLN_TX1_083
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

/-- Row root on its own input domain, ruling (bf). Both input arrays are
arbitrary; the loop resets only the occupied count. Ten/twelve and the
9216-byte child gate are conclusions of TreePacket, not caller premises. -/
theorem root (H : Bytes → State) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (raw : Array U32 22#usize) (commitment : NLL.Root) (kind : Usize)
 (hk : kind.val<3) (canonical : ∀ j,j<22 → raw.val[j]!.val<262144)
 (rootValue : commitment=encodeState (OraclePortBatchDraft.committedRoot p kind.val)) :
 NLN.TreePacket H proof p raw commitment 0#usize kind :=
 NLN.tree H proof len p wire raw commitment 0#usize kind (by scalar_tac) hk canonical rootValue

set_option pp.proofs false
#print root
#print axioms root
end NLN_TX1_083
end
