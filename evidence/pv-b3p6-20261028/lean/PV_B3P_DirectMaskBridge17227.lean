import PV_B3P_DirectMask17_1749227
import PV_B3P_DirectMask17_2048227
import PV_B3P_DirectMask17_2049227
import PV_B3P_DirectMask17_4097227
import PV_B3P_DirectMask17_6144227
import PV_B3P_DirectMask17_6145227
import PV_B3P_DirectMask17_26214227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Success227 PV_B3P_Correct14227 Result
set_option autoImplicit false

/-- These are outstanding source laws for the two extracted externals.
This structure is not installed as a native instance or an endpoint premise. -/
structure MaskIntegerLaws17 (ones zeros : U16 → Result U32) : Prop where
  count_1749 : ones 1749#u16 = .ok 7#u32
  count_2048 : ones 2048#u16 = .ok 1#u32
  count_2049 : ones 2049#u16 = .ok 2#u32
  count_4097 : ones 4097#u16 = .ok 2#u32
  count_6144 : ones 6144#u16 = .ok 2#u32
  count_6145 : ones 6145#u16 = .ok 3#u32
  count_26214 : ones 26214#u16 = .ok 8#u32
  trail_1024 : zeros 1024#u16 = .ok 10#u32
  trail_1536 : zeros 1536#u16 = .ok 9#u32
  trail_1664 : zeros 1664#u16 = .ok 7#u32
  trail_1728 : zeros 1728#u16 = .ok 6#u32
  trail_1744 : zeros 1744#u16 = .ok 4#u32
  trail_1748 : zeros 1748#u16 = .ok 2#u32
  trail_1749 : zeros 1749#u16 = .ok 0#u32
  trail_2048 : zeros 2048#u16 = .ok 11#u32
  trail_2049 : zeros 2049#u16 = .ok 0#u32
  trail_4096 : zeros 4096#u16 = .ok 12#u32
  trail_4097 : zeros 4097#u16 = .ok 0#u32
  trail_6144 : zeros 6144#u16 = .ok 11#u32
  trail_6145 : zeros 6145#u16 = .ok 0#u32
  trail_16384 : zeros 16384#u16 = .ok 14#u32
  trail_24576 : zeros 24576#u16 = .ok 13#u32
  trail_25600 : zeros 25600#u16 = .ok 10#u32
  trail_26112 : zeros 26112#u16 = .ok 9#u32
  trail_26176 : zeros 26176#u16 = .ok 6#u32
  trail_26208 : zeros 26208#u16 = .ok 5#u32
  trail_26212 : zeros 26212#u16 = .ok 2#u32
  trail_26214 : zeros 26214#u16 = .ok 1#u32

theorem mask_extraction_reference_on_domain17 (ones zeros : U16 → Result U32)
    (laws : MaskIntegerLaws17 ones zeros)
    (values : Array aspis_core.field.QM31 16#usize) (mask : U16)
    (allowed : MaskAllowed mask) :
    host_copy_terminal.selector_mask_sum_16 ones zeros values mask =
      reference_copy_terminal.selector_mask_sum_16 values mask := by
  rcases allowed with h|h|h|h|h|h|h
  · subst mask
    exact mask_direct17_1749 ones zeros values laws.count_1749 laws.trail_1749 laws.trail_1748 laws.trail_1744 laws.trail_1728 laws.trail_1664 laws.trail_1536 laws.trail_1024
  · subst mask
    exact mask_direct17_2048 ones zeros values laws.count_2048 laws.trail_2048
  · subst mask
    exact mask_direct17_2049 ones zeros values laws.count_2049 laws.trail_2049 laws.trail_2048
  · subst mask
    exact mask_direct17_4097 ones zeros values laws.count_4097 laws.trail_4097 laws.trail_4096
  · subst mask
    exact mask_direct17_6144 ones zeros values laws.count_6144 laws.trail_6144 laws.trail_4096
  · subst mask
    exact mask_direct17_6145 ones zeros values laws.count_6145 laws.trail_6145 laws.trail_6144 laws.trail_4096
  · subst mask
    exact mask_direct17_26214 ones zeros values laws.count_26214 laws.trail_26214 laws.trail_26212 laws.trail_26208 laws.trail_26176 laws.trail_26112 laws.trail_25600 laws.trail_24576 laws.trail_16384

def mask_ones_model17 (mask : U16) : Result U32 :=
  if mask = 1749#u16 then .ok 7#u32 else
  if mask = 2048#u16 then .ok 1#u32 else
  if mask = 2049#u16 then .ok 2#u32 else
  if mask = 4097#u16 then .ok 2#u32 else
  if mask = 6144#u16 then .ok 2#u32 else
  if mask = 6145#u16 then .ok 3#u32 else
  if mask = 26214#u16 then .ok 8#u32 else
  .ok 0#u32

def mask_zeros_model17 (mask : U16) : Result U32 :=
  if mask = 1024#u16 then .ok 10#u32 else
  if mask = 1536#u16 then .ok 9#u32 else
  if mask = 1664#u16 then .ok 7#u32 else
  if mask = 1728#u16 then .ok 6#u32 else
  if mask = 1744#u16 then .ok 4#u32 else
  if mask = 1748#u16 then .ok 2#u32 else
  if mask = 1749#u16 then .ok 0#u32 else
  if mask = 2048#u16 then .ok 11#u32 else
  if mask = 2049#u16 then .ok 0#u32 else
  if mask = 4096#u16 then .ok 12#u32 else
  if mask = 4097#u16 then .ok 0#u32 else
  if mask = 6144#u16 then .ok 11#u32 else
  if mask = 6145#u16 then .ok 0#u32 else
  if mask = 16384#u16 then .ok 14#u32 else
  if mask = 24576#u16 then .ok 13#u32 else
  if mask = 25600#u16 then .ok 10#u32 else
  if mask = 26112#u16 then .ok 9#u32 else
  if mask = 26176#u16 then .ok 6#u32 else
  if mask = 26208#u16 then .ok 5#u32 else
  if mask = 26212#u16 then .ok 2#u32 else
  if mask = 26214#u16 then .ok 1#u32 else
  .ok 0#u32

/-- Consistency only. This finite mathematical model does not bind the Rust
intrinsics, and earns no native source-law credit. -/
theorem mask_integer_laws_consistent17 :
    MaskIntegerLaws17 mask_ones_model17 mask_zeros_model17 := by
  constructor <;> rfl

#print axioms mask_extraction_reference_on_domain17
#print axioms mask_integer_laws_consistent17
end PV_B3P_Direct17227
