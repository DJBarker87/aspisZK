import NLL_ParentAbort
import NLL_ValuesReturning
set_option autoImplicit false
noncomputable section
namespace NLL_ValuesAbort
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem source (H : Bytes → State) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (raw : Array U32 22#usize) (roots : Roots) (batch : Usize) (hb : batch.val<2)
 (canonical : ∀ j,j<22 → raw.val[j]!.val<262144)
 (history : NLL.History) (pending : Pending)
 (native : AbortValues H proof raw roots batch history pending) :
 NLL_Prefix.At (plan H proof p raw batch (sites roots) NKV_ParentSource.zeroI NKV_ParentSource.zeroV)
   (history++pending.answered) pending.parts :=
 NLL_ParentAbort.calls H proof len p wire raw batch hb canonical (sites roots) (NLL_ValuesReturning.kinds roots)
   NKV_ParentSource.zeroI NKV_ParentSource.zeroV history pending native

set_option pp.proofs false
#print source
#print axioms source
end NLL_ValuesAbort
end
