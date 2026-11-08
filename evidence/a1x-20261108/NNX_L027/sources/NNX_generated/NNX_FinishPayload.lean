import NNV_ResultOkPort
import NNX_ArrayRead
import NNV_FinishTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_FinishPayload
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers

theorem source (p : Prefix) (row : U8) (bytes : RSL.Bytes)
 (called : LIB_VRecordsAll.payload p row.val = .ok bytes) :
 ∃ raw : Slice U8, FinishModel.payload (prefixRaw p) row = .ok (.Ok raw) ∧
 LIB_Carriers.bytes raw = bytes := by
 have mapped := LIB_VRecordsAll.payload_native p row
 rw [called] at mapped
 obtain ⟨reply,native,image⟩ := NNV_ResultOkPort.mapped _ _ _ mapped
 cases reply with
 | Err e => cases image
 | Ok raw => exact ⟨raw,native,Except.ok.inj image⟩
#print axioms source
end AspisR1.NNX_FinishPayload
end
