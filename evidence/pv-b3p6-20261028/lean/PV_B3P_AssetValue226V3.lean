import PV_B3P_NativeFieldByte226V3
import PV_B3P_Regions226V3
import PV_B3P_Offset226V3
namespace PV_B3P_AssetValue226V3
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false

theorem complete_result (p : reference226.OwnedPublic) (i : Usize)
    (lo : 65 ≤ i.val) (hi : i.val < 69) :
    reference226.byte_at p i =
      if p.asset_id < 2147483647#u32 then .ok (.Ok
        ((core.num.U32.to_le_bytes p.asset_id).val[(Usize.wrapping_sub i 65#usize).val]'(by
          rw [(core.num.U32.to_le_bytes p.asset_id).property,
            PV_B3P_Offset226V3.sub_value _ _ (by simpa using lo)]
          scalar_tac)))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  rw [PV_B3P_Regions226V3.asset p i lo hi]
  apply PV_B3P_NativeFieldByte226V3.complete_result
  rw [PV_B3P_Offset226V3.sub_value _ _ (by simpa using lo)]
  scalar_tac

#print axioms complete_result
end PV_B3P_AssetValue226V3
