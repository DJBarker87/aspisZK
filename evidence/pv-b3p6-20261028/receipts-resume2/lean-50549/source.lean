import PV_B3P_BlockProjection226
import PV_B3P_EncodeLength226
import PV_B3P_ByteCellValue226
import PV_B3P_ChunkFlatten226
namespace PV_B3P_WholeBuffer226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_ByteLayout226V3
set_option autoImplicit false
attribute [local irreducible] reference226.byte_at reference226.chunk reference226.chunk8 layout
set_option backward.isDefEq.respectTransparency false in
theorem cells (p : reference226.OwnedPublic)
    (chunks : PV_B3P_ByteOutput226.Chunks) (n : Usize)
    (h : reference226.encode_owned p = .ok (.Ok (chunks,n)))
    (i : Nat) (hi : i < (layout p).length) :
    (PV_B3P_ByteOutput226.flatten chunks)[i]? = (layout p)[i]? := by
  have hlen := layout_length p
  have hi1472 : i < 1472 := by split at hlen <;> omega
  have hq : i/64 < 23 := by omega
  let r : Usize := Usize.ofNatCore (i%64) (by
    have hb := Usize.cMax_bound_concrete.1
    scalar_tac)
  let idx : Usize := Usize.ofNatCore i (by
    have hb := Usize.cMax_bound_concrete.1
    scalar_tac)
  have hrval : r.val = i%64 := rfl
  have hival : idx.val = i := rfl
  have hr : r.val < 64 := by rw [hrval]; omega
  have hc := PV_B3P_EncodeSuccess226.success_chunk p chunks n h (i/64) hq
  have hb : (PV_B3P_EncodeSuccess226.start (i/64) hq).val + 64 < UScalar.size .Usize := by
    rw [PV_B3P_EncodeSuccess226.start_val,UScalar.size_def]
    have hmax := Usize.cMax_bound_concrete.1
    scalar_tac
  have hv := PV_B3P_BlockProjection226.success_cell p
    (PV_B3P_EncodeSuccess226.start (i/64) hq) _ hc hb r hr
  have hadd : Usize.wrapping_add (PV_B3P_EncodeSuccess226.start (i/64) hq) r = idx := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value _ _ (by omega),
      PV_B3P_EncodeSuccess226.start_val,hrval,hival]
    omega
  rw [hadd] at hv
  have hval := PV_B3P_ByteCellValue226.success_value p idx _ hv (by rw [hival]; exact hi)
  rw [hival,List.getElem?_eq_getElem hi] at hval
  simp only [Option.getD_some] at hval
  rw [PV_B3P_ChunkFlatten226.flatten_cell chunks i hi1472,
    List.getElem?_eq_getElem (by rw [(chunks.val[i/64]'(by rw [chunks.property]; simpa using hq)).property]; omega),
    List.getElem?_eq_getElem hi]
  exact congrArg some hval

set_option backward.isDefEq.respectTransparency false in
theorem value (p : reference226.OwnedPublic)
    (chunks : PV_B3P_ByteOutput226.Chunks) (n : Usize)
    (h : reference226.encode_owned p = .ok (.Ok (chunks,n))) :
    (PV_B3P_ByteOutput226.bytes chunks n).val = layout p := by
  apply PV_B3P_ChunkFlatten226.take_value chunks n (layout p)
  · rw [PV_B3P_EncodeLength226.success_length p chunks n h,layout_length]
    cases p.withdrawal <;> rfl
  · rw [layout_length]
    split <;> omega
  · exact cells p chunks n h
#print axioms cells
#print axioms value
end PV_B3P_WholeBuffer226
