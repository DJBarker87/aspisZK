import NNG_LIBData
import NNG_InstallRecord
import NNG_InstallPayload
import NNG_ModelDecode
import LIB_VRecordsAll
import NNG_EmittedCallGraph
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBRecords
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_LIBScalar NNG_LIBArrays
open AspisR1.NMT_Transport (arr)

def recordReply : core.result.Result r1_wire.ValidatedRecord r1_wire.Error → Except LIB_VCarriers.WErr LIB_VCarriers.Record
 | .Ok r => .ok (toT14 r) | .Err e => .error (toT13 e)
def payloadReply : core.result.Result (Slice U8) r1_wire.Error → Except LIB_VCarriers.WErr RSL.Bytes
 | .Ok s => .ok (LIB_Carriers.bytes s) | .Err e => .error (toT13 e)
def decodeReply (fallback : Value) : core.result.Result K29 r1_wire.Error → Except LIB_VCarriers.WErr LIB_VCarriers.K29
 | .Ok a => .ok (projectArray fallback a) | .Err e => .error (toT13 e)

theorem record (p : LIB_VCarriers.Prefix) (row : U8) :
    NNG_EmittedCallGraph.resultMap recordReply (NNG_Install.validatedRecord (NNG_LIBData.lowerPrefix p) row) =
      .ok (LIB_VRecordsAll.validatedRecord p row.val) := by
  unfold NNG_Install.validatedRecord NNG_LIBData.lowerPrefix
  rw [fromT12_inverse,LIB_VRecords.validated_exact]
  dsimp only [LIB_VRecordsAll.validatedRecord]
  generalize LIB_VRecords.validatedRecord p row.val = out
  cases out <;> simp only [LIB_VRecords.raw,NMP_ResultTransport.outer,NMP_ResultTransport.inner,
    NNG_EmittedCallGraph.resultMap,recordReply,fromT14_inverse,fromT13_inverse]
#print axioms record

theorem payload (p : LIB_VCarriers.Prefix) (row : U8) :
    NNG_EmittedCallGraph.resultMap payloadReply (NNG_Install.payload (NNG_LIBData.lowerPrefix p) row) =
      .ok (LIB_VRecordsAll.payload p row.val) := by
  obtain ⟨out,same⟩ := LIB_VRecords.payload_total p row
  have native := LIB_VRecordsAll.payload_native p row
  rw [same,bind_tc_ok] at native
  unfold NNG_Install.payload NNG_LIBData.lowerPrefix
  rw [fromT12_inverse,same]
  cases out <;> simpa only [NMP_ResultTransport.outer,NMP_ResultTransport.inner,
    NNG_EmittedCallGraph.resultMap,payloadReply,LIB_VRecords.host,Except.map,fromT13_inverse,id_eq] using native
#print axioms payload

theorem raise_array {n : Usize} (a : Array Value n) :
    arr fromT1 (LIB_VScalarCarriers.array LIB_VScalarCarriers.toRaw a) = lowerArray a := by
  apply Subtype.ext
  simp only [arr,LIB_VScalarCarriers.array,lowerArray,lower,List.map_map,Function.comp_def]
  rfl
#print axioms raise_array

end AspisR1.NNG_LIBRecords
