import NNV_FinishDecodeDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_FinishDecodePort
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers
/-- Both historical adapters close over the SAME emitted decoder; compare
only their nominal source/result carrier maps. -/
theorem source (n : Usize) (record : Record) (offset : Usize) :
 AspisS1ExtractedRoundChildren.decodeMain n record offset =
 RawActualDecodeKMainAdapter.decodeMain n record offset := by
 rfl

theorem returned (r : Record) (off : Usize) (out : K29)
 (domain : LIB_VDecode.Domain r off.val)
 (called : LIB_VRecordsAll.decodeK29 r off.val = .ok out) :
 AspisS1ExtractedRoundChildren.decodeMain 29#usize r off = .ok (.Ok (k29Raw out)) := by
 rw [source]
 exact NNV_FinishDecode.returned r off out domain called
#print axioms source
#print axioms returned
end AspisR1.NNX_FinishDecodePort
end
