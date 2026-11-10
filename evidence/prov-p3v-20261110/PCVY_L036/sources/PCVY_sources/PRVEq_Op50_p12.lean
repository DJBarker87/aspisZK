import Aeneas
import NCV_Reference.Funs
import PCVV_LaneDecodeRef
import PRVEq_Op50_p11
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVY_Op50
open PCVV_LaneDecodeRef (sl le at' K Lane frontierLoop decodeLane)

/-! ## 10. The transcription's header and tree guards in terms of the Aeneas bytes -/

/-- byte `i` of the slice, 0 outside -/
def g (b : Slice U8) (i : Nat) : U8 := b.val.getD i 0#u8

theorem at_g (b : Slice U8) (i : Nat) : at' (bytesOf b) i = bt (g b i) := by
  unfold at' bytesOf g
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases b.val[i]? with
  | none => first | rfl | simp [bt]
  | some x => rfl

theorem bt_eq_iff (x y : U8) : bt x = bt y ↔ x = y :=
  ⟨fun h => bt_inj x y h, fun h => by rw [h]⟩

theorem bt_zero : bt 0#u8 = 0 := by first | rfl | decide | simp [bt]

theorem bne_bt (x y : U8) (m : UInt8) (h : bt y = m) : (bt x != m) = false ↔ x = y := by
  subst h
  rw [bne_eq_false_iff_eq, bt_eq_iff]

theorem bne_blit (l m : List U8) (ml : List UInt8) (h : m.map bt = ml) :
    (l.map bt != ml) = false ↔ l = m := by
  rw [bne_lit l m ml h]
  simp

theorem sl_slg (b : Slice U8) (a c : Nat) : sl (bytesOf b) a c = (slg b.val a c).map bt := by
  unfold bytesOf
  exact sl_map bt b.val a c

def mag : List U8 := [65#u8, 83#u8, 76#u8, 56#u8]
def tmag : List U8 := [65#u8, 83#u8, 80#u8, 84#u8]

/-- the eight header conditions in the order of the Rust guard (r1_pool_adapter.rs 452-461),
each stated on the Aeneas bytes -/
def HdrOK (b : Slice U8) : Prop :=
  b.val.length = 768 ∧ slg b.val 0 4 = mag ∧ g b 4 = 2#u8 ∧ (g b 5).val < 8 ∧ g b 6 = 8#u8 ∧
    g b 7 = 20#u8 ∧ slg b.val 8 40 = NCV_Reference.BINDING.val ∧ Zs (slg b.val 73 80)

theorem hdrBad_false_iff (b : Slice U8) : hdrBad K0 (bytesOf b) = false ↔ HdrOK b := by
  have a0 : ((bytesOf b).length != K0.accountBytes) = false ↔ b.val.length = 768 := by
    rw [bne_eq_false_iff_eq]
    show (bytesOf b).length = 768 ↔ _
    simp [bytesOf]
  have a1 : (sl (bytesOf b) 0 4 != K0.laneMagic) = false ↔ slg b.val 0 4 = mag := by
    rw [sl_slg]; exact bne_blit _ _ _ lit_magic
  have a2 : (at' (bytesOf b) 4 != K0.laneVersion) = false ↔ g b 4 = 2#u8 := by
    rw [at_g]; exact bne_bt _ _ _ (by first | rfl | decide | simp [bt, K0])
  have a3 : (decide ((at' (bytesOf b) 5).toNat ≥ K0.laneCount)) = false ↔ (g b 5).val < 8 := by
    rw [at_g, bt_toNat]
    show decide ((g b 5).val ≥ 8) = false ↔ _
    simp
  have a4 : (at' (bytesOf b) 6 != UInt8.ofNat K0.laneCount) = false ↔ g b 6 = 8#u8 := by
    rw [at_g]; exact bne_bt _ _ _ (by first | rfl | decide | simp [bt, K0])
  have a5 : (at' (bytesOf b) 7 != UInt8.ofNat K0.treeDepth) = false ↔ g b 7 = 20#u8 := by
    rw [at_g]; exact bne_bt _ _ _ (by first | rfl | decide | simp [bt, K0])
  have a6 : (sl (bytesOf b) 8 40 != K0.accountFormatBinding) = false ↔
      slg b.val 8 40 = NCV_Reference.BINDING.val := by
    rw [sl_slg]; exact bne_blit _ _ _ lit_binding
  have a7 : ((sl (bytesOf b) 73 K0.headerBytes).any (fun byte => byte != 0)) = false ↔
      Zs (slg b.val 73 80) := by
    show ((sl (bytesOf b) 73 80).any (fun byte => byte != 0)) = false ↔ _
    rw [sl_slg, Bool.eq_false_iff]
    simp only [List.any_map, ne_eq, List.any_eq_true, Function.comp, Zs, not_exists, not_and,
      Bool.not_eq_true]
    constructor
    · intro h x hx
      have := h x hx
      rw [bne_eq_false_iff_eq] at this
      exact (bt_eq_iff x 0#u8).1 (this.trans bt_zero.symm)
    · intro h x hx
      rw [bne_eq_false_iff_eq]
      rw [h x hx, bt_zero]
  unfold hdrBad HdrOK
  simp only [Bool.or_eq_false_iff, a0, a1, a2, a3, a4, a5, a6, a7, and_assoc]

#print axioms hdrBad_false_iff

end PCVY_Op50
