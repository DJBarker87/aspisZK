import PV_B3P_E227_12
import PV_B3P_Mask227
import PV_B3P_NineUnroll9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

def mask_read10 (values : Array aspis_core.field.QM31 16#usize) : Nat → Result aspis_core.field.QM31
  | 0 => Array.index_usize values 0#usize
  | 1 => Array.index_usize values 1#usize
  | 2 => Array.index_usize values 2#usize
  | 3 => Array.index_usize values 3#usize
  | 4 => Array.index_usize values 4#usize
  | 5 => Array.index_usize values 5#usize
  | 6 => Array.index_usize values 6#usize
  | 7 => Array.index_usize values 7#usize
  | 8 => Array.index_usize values 8#usize
  | 9 => Array.index_usize values 9#usize
  | 10 => Array.index_usize values 10#usize
  | 11 => Array.index_usize values 11#usize
  | 12 => Array.index_usize values 12#usize
  | 13 => Array.index_usize values 13#usize
  | 14 => Array.index_usize values 14#usize
  | 15 => Array.index_usize values 15#usize
  | _ => .fail Error.arrayOutOfBounds

def mask_step10 (values : Array aspis_core.field.QM31 16#usize)
    (sum : aspis_core.field.QM31) (index : Nat) : Result aspis_core.field.QM31 := do
  let value ← mask_read10 values index
  aspis_core.field.QM31.add sum value
end PV_B3P_Binding10227
