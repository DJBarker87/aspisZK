import PV_B3P_BytesV3Emission226
namespace PV_B3P_Padding226
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false

theorem value (p : reference226.OwnedPublic) (i : Usize)
    (hi : (if p.withdrawal then 1427 else 1455) ≤ i.val) :
    reference226.byte_at p i = .ok (.Ok 0#u8) := by
  cases hw : p.withdrawal with
  | false =>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at hi
    have hb : i ≥ 1455#usize := by scalar_tac
    simp only [reference226.byte_at,hw,Bool.false_eq_true,↓reduceIte,hb]
  | true =>
    simp only [hw,↓reduceIte] at hi
    have hb : i ≥ 1427#usize := by scalar_tac
    simp only [reference226.byte_at,hw,↓reduceIte,hb]
#print axioms value
end PV_B3P_Padding226
