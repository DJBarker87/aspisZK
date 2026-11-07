import NNG_LIBRecords
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBDecode
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_LIBScalar NNG_LIBArrays NNG_LIBRecords
open AspisR1.NMT_Transport (arr)

theorem decode (fallback : Value) (r : r1_wire.ValidatedRecord) (off : Usize)
    (domain : NGO_CallerDomains.Call r.row.val (29#usize).val off.val)
    (framed : r.framed.val.length=5+NFU_PacketDomains.payloadSize r.row.val) :
    NNG_EmittedCallGraph.resultMap (decodeReply fallback) (NNG_ModelDecode.call 29#usize r off) =
      .ok (LIB_VRecordsAll.decodeK29 (toT14 r) off.val) := by
  unfold NNG_ModelDecode.call
  rw [LIB_VRecordsAll.decode_native (toT14 r) off domain framed]
  dsimp only [LIB_VRecordsAll.decodeK29]
  generalize LIB_VDecode.decodeK29 (toT14 r) off.val = out
  cases out with
  | error e =>
    simp only [Except.map,LIB_VRecords.raw,NMP_ResultTransport.outer,NMP_ResultTransport.inner,
      NNG_EmittedCallGraph.resultMap,decodeReply,fromT13_inverse]
  | ok a =>
    change (Result.ok (Except.ok (projectArray fallback (arr fromT1 (LIB_VCarriers.k29Raw a)))) : Result (Except LIB_VCarriers.WErr LIB_VCarriers.K29)) = Result.ok (Except.ok a)
    unfold LIB_VCarriers.k29Raw
    rw [raise_array,project_lower_array]
#print axioms decode
end AspisR1.NNG_LIBDecode
