import NLL_ParentReturning
import NLL_ParentSource
set_option autoImplicit false
noncomputable section
namespace NLL_ValuesReturning
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem kinds (roots : Roots) : ∀ c∈sites roots,c.2.val<3 := by
 intro c mem
 simp only [sites,List.mem_cons,List.mem_singleton] at mem
 rcases mem with rfl|rfl|rfl <;> scalar_tac

theorem source (H : Bytes → State) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (raw : Array U32 22#usize) (roots : Roots) (batch : Usize) (hb : batch.val<2)
 (canonical : ∀ j,j<22 → raw.val[j]!.val<262144)
 (history : NLL.History) (out : NLL.Reply)
 (native : NLL_Parent.Invocation H proof raw roots batch history out) :
 NKV_FRef.verifier.candidate.batch_merkle_values (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
   proof raw roots batch ()=ok out ∧
 plan H proof p raw batch (sites roots) NKV_ParentSource.zeroI NKV_ParentSource.zeroV=history := by
 have packet:=NLL_ParentReturning.calls H proof len p wire raw batch hb canonical (sites roots) (kinds roots)
   NKV_ParentSource.zeroI NKV_ParentSource.zeroV history out native
 rw [NLL_ParentSource.source]
 exact packet

set_option pp.proofs false
#print source
#print axioms kinds
#print axioms source
end NLL_ValuesReturning
end
