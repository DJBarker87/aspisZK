import PV_B3P_LayoutOffsets226
import PV_B3P_ByteScalar226V3
namespace PV_B3P_ScalarRegions226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_LayoutOffsets226
set_option autoImplicit false

theorem recipient_tag (p : reference226.OwnedPublic) :
    reference226.byte_at p 69#usize = .ok (.Ok (if p.withdrawal then 0#u8 else 1#u8)) := by
  cases hw : p.withdrawal <;> simp [reference226.byte_at,hw,lift,bind_tc_ok]
#print axioms recipient_tag

theorem withdrawal_tag (p : reference226.OwnedPublic) :
    reference226.byte_at p (if p.withdrawal then 102#usize else 134#usize) =
    .ok (.Ok (if p.withdrawal then 1#u8 else 0#u8)) := by
  cases hw : p.withdrawal with
  | false =>
    simp [reference226.byte_at,hw,lift,bind_tc_ok,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9]
    intro h
    have hm := Nat.mod_le 134 Usize.size
    omega
  | true =>
    simp [reference226.byte_at,hw,lift,bind_tc_ok,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9]
    intro h
    have hm := Nat.mod_le 102 Usize.size
    omega
#print axioms withdrawal_tag
theorem amount (p : reference226.OwnedPublic) (i : Usize) (hw : p.withdrawal = true)
    (lo : 103 ≤ i.val) (hi : i.val < 107) :
    reference226.byte_at p i = reference226.field_byte p.withdrawal_amount
      (Usize.wrapping_sub i 103#usize) := by
  have h0 : ¬ (i ≥ 1427#usize) := by scalar_tac
  have h1 : ¬ (i = 0#usize) := by scalar_tac
  have h2 : ¬ (i < 33#usize) := by scalar_tac
  have h3 : ¬ (i < 65#usize) := by scalar_tac
  have h4 : ¬ (i < 69#usize) := by scalar_tac
  have h5 : ¬ (i = 69#usize) := by scalar_tac
  have h6 : ¬ (i < 70#usize) := by scalar_tac
  have h7 : ¬ (i < 102#usize) := by scalar_tac
  have h8 : ¬ (i = 102#usize) := by scalar_tac
  have h9 : i < 107#usize := by scalar_tac
  simp only [reference226.byte_at,hw,↓reduceIte,lift,bind_tc_ok,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
#print axioms amount
def indexLane (v : U64) (j : Usize) : U8 :=
  UScalar.cast .U8 (U64.wrapping_shr v
    (U32.wrapping_mul 8#u32 (UScalar.cast .U32 j)))

theorem index (p : reference226.OwnedPublic) (i : Usize)
    (lo : (if p.withdrawal then 107 else 135) ≤ i.val)
    (hi : i.val < (if p.withdrawal then 115 else 143)) :
    reference226.byte_at p i = .ok (.Ok (indexLane p.next_pair_index
      (Usize.wrapping_sub i (if p.withdrawal then 107#usize else 135#usize)))) := by
  cases hw : p.withdrawal with
  | false =>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have h0 : ¬ (i ≥ 1455#usize) := by scalar_tac
    have h1 : ¬ (i = 0#usize) := by scalar_tac
    have h2 : ¬ (i < 33#usize) := by scalar_tac
    have h3 : ¬ (i < 65#usize) := by scalar_tac
    have h4 : ¬ (i < 69#usize) := by scalar_tac
    have h5 : ¬ (i = 69#usize) := by scalar_tac
    have h6 : ¬ (i < 102#usize) := by scalar_tac
    have h7 : ¬ (i < 134#usize) := by scalar_tac
    have h8 : ¬ (i = 134#usize) := by scalar_tac
    have h9 : ¬ (i < 135#usize) := by scalar_tac
    have h10 : i < 143#usize := by scalar_tac
    simp only [reference226.byte_at,hw,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,indexLane,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]
  | true =>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have h0 : ¬ (i ≥ 1427#usize) := by scalar_tac
    have h1 : ¬ (i = 0#usize) := by scalar_tac
    have h2 : ¬ (i < 33#usize) := by scalar_tac
    have h3 : ¬ (i < 65#usize) := by scalar_tac
    have h4 : ¬ (i < 69#usize) := by scalar_tac
    have h5 : ¬ (i = 69#usize) := by scalar_tac
    have h6 : ¬ (i < 70#usize) := by scalar_tac
    have h7 : ¬ (i < 102#usize) := by scalar_tac
    have h8 : ¬ (i = 102#usize) := by scalar_tac
    have h9 : ¬ (i < 107#usize) := by scalar_tac
    have h10 : i < 115#usize := by scalar_tac
    simp only [reference226.byte_at,hw,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,indexLane,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]
#print axioms index

theorem padding (p : reference226.OwnedPublic) (i : Usize)
    (lo : (if p.withdrawal then 1427 else 1455) ≤ i.val) :
    reference226.byte_at p i = .ok (.Ok 0#u8) := by
  cases hw : p.withdrawal with
  | false =>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo
    have hn : i ≥ 1455#usize := by scalar_tac
    simp only [reference226.byte_at,hw,Bool.false_eq_true,↓reduceIte,hn,lift,bind_tc_ok]
  | true =>
    simp only [hw,↓reduceIte] at lo
    have hn : i ≥ 1427#usize := by scalar_tac
    simp only [reference226.byte_at,hw,↓reduceIte,hn,lift,bind_tc_ok]
#print axioms padding
end PV_B3P_ScalarRegions226
