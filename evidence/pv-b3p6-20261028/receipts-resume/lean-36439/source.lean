import PV_B3P_BytesV3Emission226
namespace PV_B3P_ByteScalar226V3
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false

theorem canonical_yes (v : U32) (h : v < 2147483647#u32) :
    reference226.canonical v = .ok (some v) := by
  simp only [reference226.canonical, h, ↓reduceIte]

theorem canonical_no (v : U32) (h : ¬ v < 2147483647#u32) :
    reference226.canonical v = .ok none := by
  simp only [reference226.canonical, h, ↓reduceIte]

theorem field_reject (v : U32) (j : Usize) (h : ¬ v < 2147483647#u32) :
    reference226.field_byte v j =
      .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  simp [reference226.field_byte, canonical_no v h]

theorem field_success (v : U32) (j : Usize) (h : v < 2147483647#u32) :
    reference226.field_byte v j = .ok (.Ok
      (UScalar.cast .U8 (U32.wrapping_shr v
        (U32.wrapping_mul 8#u32 (UScalar.cast .U32 j))))) := by
  simp [reference226.field_byte, canonical_yes v h, lift]

theorem padding (p : reference226.OwnedPublic) (i : Usize)
    (h : i ≥ 1455#usize) : reference226.byte_at p i = .ok (.Ok 0#u8) := by
  have hn : 1455 ≤ i.val := by scalar_tac
  have h1455 : ¬ i.val < 1455 := by omega
  have h1427 : ¬ i.val < 1427 := by omega
  cases hp : p.withdrawal <;> simp [reference226.byte_at, hp, h1455, h1427]


#print axioms canonical_yes
#print axioms canonical_no
#print axioms field_reject
#print axioms field_success
#print axioms padding
end PV_B3P_ByteScalar226V3
