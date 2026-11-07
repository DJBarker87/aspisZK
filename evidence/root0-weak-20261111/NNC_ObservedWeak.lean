import NNC_RecordTrace
set_option autoImplicit false
noncomputable section
namespace NNC_ObservedWeak
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NNC_DigestTrace

/-- Parser/None-marker have no runtime effect; common carries the complete
SAME native digest trace, including separately stopped child requests. -/
def TraceOf {H : Bytes → State} {X : Type} {a : Args X} : End H a → Trace → Prop
 | .common out, trace => NNC_RecordTrace.FromEnd out trace
 | _, trace => trace=[]

/-- Concrete native-record observation relation. It contains no caller-chosen
renderer and retains every original part list, partial reply, and stopped
request. Association of the host I.f064 to this native observer is still an
implementation obligation, not a hypothesis of the final security theorem. -/
def Observed {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (o : RSL.Obs (Except verifier.Error Unit)) : Prop :=
 ∃ outcome events trace, NMN_064.Native H s outcome events ∧ TraceOf outcome trace ∧
   o=⟨NNC_WeakSpec.exit H s.args outcome,NNC_DigestTrace.render trace⟩

theorem exists_trace {H : Bytes → State} {X : Type} {a : Args X} (outcome : End H a) :
 ∃ trace, TraceOf outcome trace := by
 cases outcome with
 | common out => exact NNC_RecordTrace.exists_end out
 | parseFail => exact ⟨[],rfl⟩
 | parseDiv => exact ⟨[],rfl⟩
 | parseReject => exact ⟨[],rfl⟩

/-- Every native outcome is represented; no rejected or independently stopped
outcome is removed. The native high-level result/event weak law is also kept. -/
theorem transport {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (domain : NNC_064Weak.Domain s.args) (outcome : End H s.args)
 (events : List (Event Ambient X)) (native : NMN_064.Native H s outcome events) :
 NNC_064Weak.Law H s.args outcome ∧ events=chronology H s outcome ∧
 ∃ trace, TraceOf outcome trace ∧ Observed H s
   ⟨NNC_WeakSpec.exit H s.args outcome,NNC_DigestTrace.render trace⟩ := by
 have weak := (NNC_064Weak.root H s domain).1 outcome events native
 obtain ⟨trace,source⟩ := exists_trace outcome
 exact ⟨weak.1,weak.2,trace,source,outcome,events,trace,native,source,rfl⟩

theorem no_write {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (o : RSL.Obs (Except verifier.Error Unit)) (native : Observed H s o)
 (c : Nat) (bytes : RSL.Bytes) : RSL.Event.write c bytes ∉ o.events := by
 obtain ⟨outcome,events,trace,native,source,rfl⟩ := native
 exact NNC_DigestTrace.no_write trace c bytes

theorem accepted_header {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (domain : NNC_064Weak.Domain s.args)
 (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest s.args.digest) s.args.hash H)
 (o : RSL.Obs (Except verifier.Error Unit)) (native : Observed H s o)
 (accepted : o.exit=.ret (.ok ())) :
 NLW_ReaderHeader.decode (MultiproofConeCanonical.bytesOf s.args.checkpoint.val)=
 some (H (MultiproofConeCanonical.bytesOf s.args.proof.val),
   H (MultiproofConeCanonical.bytesOf s.args.publicBytes.val)) := by
 obtain ⟨outcome,events,trace,native,source,rfl⟩ := native
 obtain ⟨records,rfl⟩ := NNC_WeakSpec.exit_ok H s.args outcome accepted
 exact NNC_064Weak.accepted_header H s domain oracle records events native

#print axioms exists_trace
#print axioms transport
#print axioms no_write
#print axioms accepted_header
end NNC_ObservedWeak
