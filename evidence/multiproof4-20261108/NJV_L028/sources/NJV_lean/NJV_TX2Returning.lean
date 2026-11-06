import NJV_EntryABI
import NJV_UnitDomain
import NJV_LevelDomains
import NJV_ChildArguments

set_option autoImplicit false
noncomputable section
namespace NJV_TX2Returning
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier
open MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.MultiproofConePhysicalTransport

/-- TX2:093's actual binary entry at its original arrays, count, root and byte
slice. No TX1 input or selected alternative execution is used. -/
def entry (root : RefDigest) (physical : Slice U8) (idx : Array U32 16#usize)
    (val : Array RefDigest 16#usize) (n : Usize) :=
 NJV_Entry.program root physical (NJV_EntryABI.initial idx val n)

def endpoint (root : RefDigest) (physical : Slice U8) (idx : Array U32 16#usize)
    (val : Array RefDigest 16#usize) (n : Usize) :=
 AspisR1.MultiproofConeVerifyState.verifyState root physical (NJV_EntryABI.initial idx val n)

/-- The complete returning certificate is actually stronger than the ten-leaf
unit domain: the frozen entry rejects malformed counts/order itself. Thus the
TX2 <=12 case is NOT silently strengthened to <=10. Unit clauses remain on
its SAME batch1/tree caller, as recorded in NJV_CALLER_CLAUSES.json. -/
theorem returning (H : Bytes → State) (root : RefDigest) (physical : Slice U8)
    (idx : Array U32 16#usize) (val : Array RefDigest 16#usize) (n : Usize)
    (bytes : physical.val.length≤9216)
    (events : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (out : Bool × NJP_RowModel.Scratch)
    (native : NJV_NativeEntry.Invocation (NJP_RequestTransport.hash (rawOracle H))
      root physical (NJV_EntryABI.initial idx val n) events out) :
 let adopted := eval H (endpoint root physical idx val n)
 (adopted.1,ok (NJP_CohortReturning.answer adopted.2))=
 (NJV_AdoptedObservation.history events,ok out) :=
 NJV_AdoptedObservation.returning H root physical (NJV_EntryABI.initial idx val n) rfl bytes events out native

theorem unit_returning (H : Bytes → State) (root : RefDigest) (physical slot : Slice U8)
    (idx : Array U32 16#usize) (val : Array RefDigest 16#usize) (n : Usize)
    (domain : NJV_UnitDomain.Domain physical slot (NJV_EntryABI.initial idx val n))
    (events : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (out : Bool × NJP_RowModel.Scratch)
    (native : NJV_NativeEntry.Invocation (NJP_RequestTransport.hash (rawOracle H))
      root physical (NJV_EntryABI.initial idx val n) events out) :
 let adopted := eval H (endpoint root physical idx val n)
 (adopted.1,ok (NJP_CohortReturning.answer adopted.2))=
 (NJV_AdoptedObservation.history events,ok out) :=
 returning H root physical idx val n (NJV_UnitDomain.bytes _ _ _ domain) events out native

#print returning
#print axioms returning
#print unit_returning
#print axioms unit_returning
end NJV_TX2Returning
end
