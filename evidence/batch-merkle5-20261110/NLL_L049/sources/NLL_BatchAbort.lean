import NLL_BatchSource
import NLL_ValuesAbort
set_option autoImplicit false
noncomputable section
namespace NLL_BatchAbort
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def Invocation (H : Bytes → State) (proof : Slice U8) (p : verifier.Prepared)
 (folded : NLL.Root) (batch : Usize) (history : NLL.History) (pending : Pending) : Prop :=
 AbortValues H proof p.queries (NLL_BatchSource.roots p folded) batch history pending

theorem source (H : Bytes → State) (proof : Slice U8) (len : proof.val.length=57607)
 (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=MultiproofConeCanonical.bytesOf proof.val)
 (p : verifier.Prepared) (folded : NLL.Root) (batch : Usize) (hb : batch.val<2)
 (canonical : ∀ j,j<22 → p.queries.val[j]!.val<262144)
 (history : NLL.History) (pending : Pending)
 (native : Invocation H proof p folded batch history pending) :
 NLL_Prefix.At (plan H proof parsed p.queries batch (sites (NLL_BatchSource.roots p folded))
   NKV_ParentSource.zeroI NKV_ParentSource.zeroV) (history++pending.answered) pending.parts :=
 NLL_ValuesAbort.source H proof len parsed wire p.queries _ batch hb canonical history pending native

set_option pp.proofs false
#print source
#print axioms source
end NLL_BatchAbort
end
