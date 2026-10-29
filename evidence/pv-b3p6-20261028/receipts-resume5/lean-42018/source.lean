import PV_B3P_CompleteTypes227
namespace PV_B3P_Discriminant227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

/-- The two source constructors have implicit discriminants zero and one. -/
def copy_read : reference_copy_terminal.PoolV1PairForestCompiledVariantV1 → Isize
  | .PrivateTransfer => 0#isize
  | .Withdrawal => 1#isize

instance : Discriminant reference_copy_terminal.PoolV1PairForestCompiledVariantV1 Isize where
  read_discriminant := copy_read

theorem transfer_tag : copy_read .PrivateTransfer = 0#isize := rfl
theorem withdrawal_tag : copy_read .Withdrawal = 1#isize := rfl

#print axioms transfer_tag
#print axioms withdrawal_tag
end PV_B3P_Discriminant227
