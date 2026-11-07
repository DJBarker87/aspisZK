import NNC_C04StopEvents
import NNC_DigestTrace
set_option autoImplicit false
noncomputable section
namespace NNC_C04Trace
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NNC_DigestTrace

/-- Exact native C04 trace decoration. Every returning/stopped child remains
at its SAME native proof/prepared/folded arguments, with no canonical-root law. -/
def FromDetail {H : Bytes → State} {e : Event}
 (detail : NLT_Subcuts.Detail H e) (trace : Trace) : Prop :=
 match detail with
 | .ordinary _ _ => trace=[]
 | .returning pr p folded reply inside out _ =>
   ∃ log, NNC_C04Events.Returned H pr p.queries 1#usize
     (NLL_Parent.sites (NLL_BatchSource.roots p folded)) NKV_ParentSource.zeroI NKV_ParentSource.zeroV
     inside out log ∧ trace=log.map Step.attempted
 | .aborting pr p folded error inside pending _ =>
   ∃ log, NNC_C04StopEvents.Stopped H pr p.queries 1#usize
     (NLL_Parent.sites (NLL_BatchSource.roots p folded)) NKV_ParentSource.zeroI NKV_ParentSource.zeroV
     inside pending log ∧ trace=log.map Step.attempted++[.pending pending.parts]

def answered {H : Bytes → State} {e : Event} : NLT_Subcuts.Detail H e → NLL.History
 | .ordinary _ _ => []
 | .returning _ _ _ _ inside _ _ => inside
 | .aborting _ _ _ _ inside pending _ => inside++pending.answered

def pendingParts {H : Bytes → State} {e : Event} : NLT_Subcuts.Detail H e → List SdkC_Source.Parts
 | .ordinary _ _ => []
 | .returning .. => []
 | .aborting _ _ _ _ _ pending _ => [pending.parts]

theorem exists_trace {H : Bytes → State} {e : Event} (detail : NLT_Subcuts.Detail H e) :
 ∃ trace, FromDetail detail trace := by
 cases detail with
 | ordinary e notMerkle => exact ⟨[],rfl⟩
 | returning pr p folded reply inside out child =>
   obtain ⟨log,native⟩ := NNC_C04Events.returning child
   exact ⟨log.map Step.attempted,log,native,rfl⟩
 | aborting pr p folded error inside pending child =>
   obtain ⟨log,native⟩ := NNC_C04StopEvents.stopped_source child
   exact ⟨log.map Step.attempted++[.pending pending.parts],log,native,rfl⟩

theorem read_trace {H : Bytes → State} {e : Event} (detail : NLT_Subcuts.Detail H e)
 (trace : Trace) (observed : FromDetail detail trace) :
 SdkC_Source.readLog (NNC_DigestTrace.log trace)=answered detail ∧
 NNC_DigestTrace.pending trace=pendingParts detail := by
 cases detail with
 | ordinary e notMerkle =>
   change trace=[] at observed
   subst trace
   exact ⟨rfl,rfl⟩
 | returning pr p folded reply inside out child =>
   obtain ⟨log,native,rfl⟩ := observed
   exact ⟨by rw [log_attempted];exact NNC_C04Events.returning_read native,no_pending log⟩
 | aborting pr p folded error inside pending child =>
   obtain ⟨log,native,rfl⟩ := observed
   have retained := NNC_DigestTrace.stopped log pending.parts
   exact ⟨by rw [retained.1];exact NNC_C04StopEvents.stopped_read native,retained.2.1⟩

#print axioms exists_trace
#print axioms read_trace
end NNC_C04Trace
