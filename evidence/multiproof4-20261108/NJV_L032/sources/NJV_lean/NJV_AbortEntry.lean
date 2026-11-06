import NJV_AbortLevels
import NJV_EntryABI

set_option autoImplicit false
noncomputable section
namespace NJV_AbortEntry
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier
open MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1.MultiproofConePhysicalTransport

/-- Same-entry native abort: guard passed, same zeroed cursor, native row cuts
until the pending boundary. No returned execution, Err, or last reply exists. -/
structure Invocation (H : NJP_RowModel.Request → NJP_RowModel.Digest)
    (root : RefDigest) (physical : Slice U8) (s : reference.Scratch)
    (events : List (NJP_RowModel.Request × NJP_RowModel.Digest))
    (q : NJP_RowModel.Request) (pending : NJP_RowModel.Scratch) : Prop where
 guard : NJV_Entry.Guard physical s
 levels : NJV_AbortLevels.Invocation H (fun n => physical.val[n]!) physical.val.length
   18 {raw s with cursor:=0} events q pending

theorem raw_prefix (H : NJP_RowModel.Request → NJP_RowModel.Digest)
    (root : RefDigest) (physical : Slice U8) (s : reference.Scratch)
    (events : List (NJP_RowModel.Request × NJP_RowModel.Digest))
    (q : NJP_RowModel.Request) (pending : NJP_RowModel.Scratch)
    (native : Invocation H root physical s events q pending) :
 NJP_AbortPrefix.pending H events.length (NJV_Entry.rawProgram root physical s)=some (events,q) := by
 simp only [NJV_Entry.rawProgram,if_pos native.guard]
 exact NJV_AbortLevels.run H _ _ _ _ _ _ _ native.levels

/-- Associate the native pending history with the exact entry's program,
including its last UNANSWERED request, at every possible call ordinal. -/
theorem physical_prefix (H : Slice (Slice U8) → RefDigest)
    (root : RefDigest) (physical : Slice U8) (s : reference.Scratch)
    (events : List (NJP_RowModel.Request × NJP_RowModel.Digest))
    (q : NJP_RowModel.Request) (pending : NJP_RowModel.Scratch)
    (native : Invocation (NJP_RequestTransport.hash H) root physical s events q pending) :
 NJP_AbortTransport.physicalPending H events.length
   (NJP_RequestTransport.transport (NJV_Entry.rawProgram root physical s))=
 some (NJP_AbortTransport.history events,NJP_RequestTransport.address q) := by
 exact (NJP_AbortTransport.abort_prefix H events.length _ events q
   (raw_prefix _ _ _ _ _ _ _ native)).1

/-- The SAME adopted endpoint has this chronological answered prefix and
this next request. H is used to compare total denotations only; the prefix
includes no answer for q and makes no runtime totality assumption. -/
theorem adopted_prefix (H : Bytes → State) (root : RefDigest) (physical : Slice U8)
    (s : reference.Scratch) (zero : s.«at»=0#usize) (bytes : physical.val.length≤9216)
    (events : List (NJP_RowModel.Request × NJP_RowModel.Digest))
    (q : NJP_RowModel.Request) (pending : NJP_RowModel.Scratch)
    (native : Invocation (NJP_RequestTransport.hash (rawOracle H)) root physical s events q pending) :
 let log := (eval H (AspisR1.MultiproofConeVerifyState.verifyState root physical s)).1
 log.take events.length=NJV_AdoptedObservation.history events ∧
 (log[events.length]?).map Prod.fst=some (flatten (NJP_RequestTransport.address q)) := by
 dsimp only
 have p := raw_prefix _ _ _ _ _ _ _ native
 obtain ⟨first,len,last⟩ := NJP_AbortPrefix.exact_prefix _ _ _ _ _ p
 have typed := NJV_Entry.observation (rawOracle H) root physical s
 dsimp only at typed
 rw [NJP_RequestTransport.observation] at typed
 have source := NJV_Entry.adopted H root physical s zero bytes
 rw [transport_observation] at source
 have sourceLogs := congrArg Prod.fst source
 have typedLogs := congrArg Prod.fst typed
 dsimp only at sourceLogs typedLogs
 have logs := sourceLogs.symm.trans
   (congrArg (List.map (fun e => (flatten e.1,decodeState e.2))) typedLogs)
 rw [logs]
 constructor
 · simp only [←List.map_take,←first,NJV_AdoptedObservation.history]
 · simp only [List.map_map,List.getElem?_map,Option.map_map,Function.comp_apply]
   simpa only [List.getElem?_map,Option.map_map,Function.comp_apply] using
     congrArg (Option.map (fun r => flatten (NJP_RequestTransport.address r))) last

#print raw_prefix
#print axioms raw_prefix
#print physical_prefix
#print axioms physical_prefix
#print adopted_prefix
#print axioms adopted_prefix
end NJV_AbortEntry
end
