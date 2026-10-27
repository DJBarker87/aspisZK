import FJc_MaskBits
import FJc_ReadSlot
import FIp_ArrayValue
import FIp_RangeNone
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_SubsetModel
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
def mask (group : Nat) : Nat :=
  match FIo_Native.weights.S2_INACTIVE_MASKS.val[group]? with
  | some m => m.val | none => 0

def sumPrefix (low : Array NE 16#usize) (group : Nat) : Nat → AspisWideTower.WideExact
  | 0 => 0
  | n+1 => sumPrefix low group n+
      if (mask group &&& 2^n)≠0 then FIp_ArrayValue.value low n else 0

theorem mask_read (group : Usize) (m : U16)
    (run : Array.index_usize FIo_Native.weights.S2_INACTIVE_MASKS group=ok m) :
    mask group.val=m.val := by
  simp only [mask,FJc_ReadSlot.slot _ group m run]
#print axioms mask_read
end AspisR1.FJc_SubsetModel
end
