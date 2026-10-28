import PV_B3P_DigestValue226V3
import PV_B3P_DigestRegions226V3
namespace PV_B3P_DigestRegionValue226V3
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_ByteLayout226V3
set_option autoImplicit false

theorem anchor (p : reference226.OwnedPublic) (i : Usize)
    (lo : 1 ≤ i.val) (hi : i.val < 33) :
    reference226.byte_at p i =
      if (p.anchor.val[(Usize.wrapping_sub i 1#usize).val / 4]?.getD 0#u32)
          < 2147483647#u32 then
        .ok (.Ok ((fields p.anchor.val)[(Usize.wrapping_sub i 1#usize).val]?.getD 0#u8))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  rw [PV_B3P_DigestRegions226V3.anchor p i lo hi]
  apply PV_B3P_DigestValue226V3.complete_result
  rw [PV_B3P_Offset226V3.sub_value _ _ (by simpa using lo)]
  scalar_tac

#print axioms anchor

theorem nullifier (p : reference226.OwnedPublic) (i : Usize)
    (lo : 33 ≤ i.val) (hi : i.val < 65) :
    reference226.byte_at p i =
      if (p.nullifier.val[(Usize.wrapping_sub i 33#usize).val / 4]?.getD 0#u32)
          < 2147483647#u32 then
        .ok (.Ok ((fields p.nullifier.val)[(Usize.wrapping_sub i 33#usize).val]?.getD 0#u8))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  rw [PV_B3P_DigestRegions226V3.nullifier p i lo hi]
  apply PV_B3P_DigestValue226V3.complete_result
  rw [PV_B3P_Offset226V3.sub_value _ _ (by simpa using lo)]
  scalar_tac

#print axioms nullifier
end PV_B3P_DigestRegionValue226V3
