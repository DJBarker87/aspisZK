import PV_B3P_DigestTotal226V3
import PV_B3P_Offset226V3
namespace PV_B3P_DigestRegions226V3
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_DigestTotal226V3
set_option autoImplicit false

theorem anchor (p : reference226.OwnedPublic) (i : Usize)
    (lo : 1 ≤ i.val) (hi : i.val < 33) :
    reference226.byte_at p i = digestAt p.anchor
      (Usize.wrapping_sub i 1#usize) := by
  have h0 : i ≠ 0#usize := by scalar_tac
  have h1427 : ¬ i ≥ 1427#usize := by scalar_tac
  have h1455 : ¬ i ≥ 1455#usize := by scalar_tac
  have h33 : i < 33#usize := by scalar_tac
  cases hp : p.withdrawal <;>
    simp only [reference226.byte_at,hp,Bool.false_eq_true,↓reduceIte,
      h0,h33,h1427,h1455,lift,bind_tc_ok,digestAt]

theorem anchor_success (p : reference226.OwnedPublic) (i : Usize)
    (lo : 1 ≤ i.val) (hi : i.val < 33)
    (hc : ∀ m ∈ p.anchor.val, m < 2147483647#u32) :
    ∃ v, reference226.byte_at p i = .ok (.Ok v) := by
  rw [anchor p i lo hi]
  apply PV_B3P_DigestTotal226V3.success _ _ _ hc
  rw [PV_B3P_Offset226V3.sub_value]
  · have hn : (1#usize).val = 1 := rfl
    rw [hn]; omega
  · simpa using lo

#print axioms anchor
#print axioms anchor_success

theorem nullifier (p : reference226.OwnedPublic) (i : Usize)
    (lo : 33 ≤ i.val) (hi : i.val < 65) :
    reference226.byte_at p i = digestAt p.nullifier
      (Usize.wrapping_sub i 33#usize) := by
  have h0 : i ≠ 0#usize := by scalar_tac
  have h1427 : ¬ i ≥ 1427#usize := by scalar_tac
  have h1455 : ¬ i ≥ 1455#usize := by scalar_tac
  have h33 : ¬ i < 33#usize := by scalar_tac
  have h65 : i < 65#usize := by scalar_tac
  cases hp : p.withdrawal <;>
    simp only [reference226.byte_at,hp,Bool.false_eq_true,↓reduceIte,
      h0,h33,h65,h1427,h1455,lift,bind_tc_ok,digestAt]

theorem nullifier_success (p : reference226.OwnedPublic) (i : Usize)
    (lo : 33 ≤ i.val) (hi : i.val < 65)
    (hc : ∀ m ∈ p.nullifier.val, m < 2147483647#u32) :
    ∃ v, reference226.byte_at p i = .ok (.Ok v) := by
  rw [nullifier p i lo hi]
  apply PV_B3P_DigestTotal226V3.success _ _ _ hc
  rw [PV_B3P_Offset226V3.sub_value]
  · have hn : (33#usize).val = 33 := rfl
    rw [hn]; omega
  · simpa using lo

#print axioms nullifier
#print axioms nullifier_success
end PV_B3P_DigestRegions226V3
