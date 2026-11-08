import NNV_FinishRecord
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_FinishDecode
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers

theorem returned (r : Record) (off : Usize) (out : K29)
 (domain : LIB_VDecode.Domain r off.val)
 (called : LIB_VRecordsAll.decodeK29 r off.val = .ok out) :
 RawActualDecodeKMainAdapter.decodeMain 29#usize r off = .ok (.Ok (k29Raw out)) := by
 have image := congrArg (fun x : Except WErr K29 => LIB_VRecords.raw (x.map k29Raw)) called
 exact (LIB_VRecordsAll.decode_native r off domain.1 domain.2).trans (congrArg Result.ok image)
#print axioms returned
end AspisR1.NNV_FinishDecode
end
