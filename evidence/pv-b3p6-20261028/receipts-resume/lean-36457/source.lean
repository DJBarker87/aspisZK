import PV_B3P_ByteOutput226
import PV_B3P_LayoutCells226V3
namespace PV_B3P_ChunkFlatten226
open Aeneas Aeneas.Std PV_B3P_ByteOutput226
set_option autoImplicit false

theorem flatten_cell (chunks : Chunks) (i : Nat) (hi : i < 1472) :
    (flatten chunks)[i]? = chunks.val[i/64].val[i%64]? := by
  have hq : i/64 < chunks.val.length := by rw [chunks.property]; scalar_tac
  have hr : i%64 < 64 := by omega
  have h := PV_B3P_LayoutCells226V3.flat_cell 64
    (fun row : Array U8 64#usize => row.val)
    (fun row => row.property) chunks.val (i/64) (i%64) hq hr
  have hid : 64*(i/64)+i%64 = i := by omega
  simpa only [flatten,hid] using h

theorem take_value (chunks : Chunks) (n : Usize) (layout : List U8)
    (hn : n.val = layout.length) (hb : layout.length ≤ 1472)
    (cells : ∀ i, i < layout.length → (flatten chunks)[i]? = layout[i]?) :
    (bytes chunks n).val = layout := by
  apply List.ext_getElem
  · rw [bytes_length,hn,Nat.min_eq_left hb]
  · intro i hi hj
    have hflat : i < (flatten chunks).length := by rw [flatten_length]; omega
    have hc := cells i hj
    rw [List.getElem?_eq_getElem hflat,List.getElem?_eq_getElem hj] at hc
    change ((flatten chunks).take n.val)[i] = layout[i]
    rw [List.getElem_take]
    exact Option.some.inj hc

theorem take_from_chunk_cells (chunks : Chunks) (n : Usize) (layout : List U8)
    (hn : n.val = layout.length) (hb : layout.length ≤ 1472)
    (cells : ∀ (q r : Nat) (hq : q < chunks.val.length), r < 64 →
      64*q+r < layout.length → chunks.val[q].val[r]? = layout[64*q+r]?) :
    (bytes chunks n).val = layout := by
  apply take_value chunks n layout hn hb
  intro i hi
  have h1472 : i < 1472 := by omega
  rw [flatten_cell chunks i h1472]
  have hq : i/64 < chunks.val.length := by rw [chunks.property]; scalar_tac
  have hid : 64*(i/64)+i%64 = i := by omega
  have hc := cells (i/64) (i%64) hq (by omega) (by omega)
  simpa only [hid] using hc

#print axioms flatten_cell
#print axioms take_value
#print axioms take_from_chunk_cells
end PV_B3P_ChunkFlatten226
