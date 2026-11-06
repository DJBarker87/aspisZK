import NJV_TX1Returning
import NJV_Admission
import NJV_AbortDomains
import NJV_CallerBounds

set_option autoImplicit false
noncomputable section
namespace NJV_TX1
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier
open MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1.MultiproofConePhysicalTransport

/-- TX1:127, returning packet. Only original native inputs, the native length
bound and reviewed native entry/row/height/terminal cuts occur as hypotheses.
All per-step domains and CLOSED child replies are discharged internally. -/
theorem TX1_127 (H : Bytes → State) (root : RefDigest) (physical : Slice U8)
    (idx : Array U32 16#usize) (val : Array RefDigest 16#usize) (n : Usize)
    (bytes : physical.val.length≤9216)
    (events : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (out : Bool × NJP_RowModel.Scratch)
    (native : NJV_NativeEntry.Invocation (NJP_RequestTransport.hash (rawOracle H))
      root physical (NJV_EntryABI.initial idx val n) events out) :
 (let adopted := eval H (NJV_TX1Returning.endpoint root physical idx val n)
  (adopted.1,ok (NJP_CohortReturning.answer adopted.2))=
    (NJV_AdoptedObservation.history events,ok out)) ∧
 NJV_Admission.Admissible (NJP_RequestTransport.hash (rawOracle H))
   root physical (NJV_EntryABI.initial idx val n) events out :=
 ⟨NJV_TX1Returning.returning H root physical idx val n bytes events out native,
  NJV_Admission.all _ _ _ _ bytes _ _ native⟩

/-- TX1:127, abort packet at any entered child. The same adopted entry has
exactly these prior replies and this next request; native pending state is
retained with its proved domain and full no-write frame. No answer for q. -/
theorem abort (H : Bytes → State) (root : RefDigest) (physical : Slice U8)
    (idx : Array U32 16#usize) (val : Array RefDigest 16#usize) (n : Usize)
    (bytes : physical.val.length≤9216)
    (events : List (NJP_RowModel.Request × NJP_RowModel.Digest))
    (q : NJP_RowModel.Request) (pending : NJP_RowModel.Scratch)
    (native : NJV_AbortEntry.Invocation (NJP_RequestTransport.hash (rawOracle H))
      root physical (NJV_EntryABI.initial idx val n) events q pending) :
 (let log := (eval H (NJV_TX1Returning.endpoint root physical idx val n)).1
  log.take events.length=NJV_AdoptedObservation.history events ∧
  (log[events.length]?).map Prod.fst=some (flatten (NJP_RequestTransport.address q))) ∧
 NJP_AbortTransport.physicalPending (rawOracle H) events.length
   (NJP_RequestTransport.transport
     (NJV_Entry.rawProgram root physical (NJV_EntryABI.initial idx val n)))=
   some (NJP_AbortTransport.history events,NJP_RequestTransport.address q) ∧
 NJV_AbortDomains.LastDomain (fun j => physical.val[j]!) physical.val.length q pending :=
 ⟨NJV_AbortEntry.adopted_prefix H root physical _ rfl bytes events q pending native,
  NJV_AbortEntry.physical_prefix (rawOracle H) root physical _ events q pending native,
  NJV_AbortDomains.entry (rawOracle H) root physical _ bytes events q pending native⟩

#print TX1_127
#print axioms TX1_127
#print abort
#print axioms abort
end NJV_TX1
end
