import NLL_ObservedCalls
import NLL_AppendPrefix
set_option autoImplicit false
noncomputable section
namespace NLL_AdoptedAbort
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem tree (H : Bytes → State) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (raw : Array U32 22#usize) (root : NLL.Root) (batch kind : Usize)
 (hb : batch.val<2) (hk : kind.val<3) (canonical : ∀ j,j<22 → raw.val[j]!.val<262144)
 (rootValue : root=encodeState (OraclePortBatchDraft.committedRoot p kind.val))
 (idx : NLL.Indices) (val : NLL.Values) (events : List Event) (pending : Pending)
 (native : AbortInvocation H proof raw root batch kind idx val events pending) :
 NLL_Prefix.At (NLL_ObservedCalls.tree H proof p raw batch kind idx val).1
   (leafHistory kind events++pending.answered) pending.parts := by
 have slot:=(NKV_BatchGeometry.slot batch kind hb hk).1
 have domain:=NLL_TerminalDomain.source H proof len p wire batch.val kind _ hb hk slot 0
 have observed:=NKV_QueryPlan.slot_history H p (Port4B_KeyInstall.queries raw) batch.val kind.val _ domain.2.1
   root rootValue (NJV_EntryABI.initial idx val 0#usize)
 change NLL_Prefix.At (eval H (MultiproofConeSlotState.slotState p (Port4B_KeyInstall.queries raw) batch.val kind.val
   (nodeView H proof (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind))
   (NJV_EntryABI.initial idx val 0#usize))).1 _ _
 rw [observed]
 exact NLL_TreeAbort.source H proof len p wire raw root batch kind hb hk canonical idx val events pending native

/-- The pending child query occurs before any possible ideal suffix.
No source model is edited when a native syscall aborts. -/
theorem bind (head : NLL.History × Result (Unit × NLL.Indices × NLL.Values))
 (k : NLL.Indices → NLL.Values → NLL.History × Result Unit)
 (answered : NLL.History) (parts : Slice (Slice U8)) (known : NLL_Prefix.At head.1 answered parts) :
 NLL_Prefix.At (NKV_ParentTrace.bindRejected head k).1 answered parts := by
 rcases head with ⟨events,result⟩
 cases result with
 | fail e => exact known
 | div => exact known
 | ok out => rcases out with ⟨u,i,v⟩;exact NLL_AppendPrefix.suffix _ _ _ _ known

#print axioms tree
#print axioms bind
end NLL_AdoptedAbort
end
