import PV_B3P_ByteScalar226V3
namespace PV_B3P_Regions226V3
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false

theorem discriminant (p : reference226.OwnedPublic) :
    reference226.byte_at p 0#usize = .ok (.Ok (if p.withdrawal then 1#u8 else 0#u8)) := by
  cases hp : p.withdrawal <;> simp [reference226.byte_at, hp]

theorem asset (p : reference226.OwnedPublic) (i : Usize)
    (lo : 65 ≤ i.val) (hi : i.val < 69) :
    reference226.byte_at p i = reference226.field_byte p.asset_id
      (Usize.wrapping_sub i 65#usize) := by
  have h0 : i ≠ 0#usize := by scalar_tac
  have h33 : ¬ i < 33#usize := by scalar_tac
  have h65 : ¬ i < 65#usize := by scalar_tac
  have h69 : i < 69#usize := by scalar_tac
  have h1427 : ¬ i ≥ 1427#usize := by scalar_tac
  have h1455 : ¬ i ≥ 1455#usize := by scalar_tac
  cases hp : p.withdrawal <;>
    simp only [reference226.byte_at,hp,Bool.false_eq_true,↓reduceIte,
      h0,h33,h65,h69,h1427,h1455,lift,bind_tc_ok]

theorem asset_rejected (p : reference226.OwnedPublic)
    (h : ¬ p.asset_id < 2147483647#u32) :
    reference226.byte_at p 65#usize =
      .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  rw [asset p 65#usize (by decide) (by decide)]
  exact PV_B3P_ByteScalar226V3.field_reject _ _ h

#print axioms discriminant
#print axioms asset
#print axioms asset_rejected
end PV_B3P_Regions226V3
