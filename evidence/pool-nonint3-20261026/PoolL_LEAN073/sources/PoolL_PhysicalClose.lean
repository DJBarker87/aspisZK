import PoolL_Physical
set_option autoImplicit false
namespace AspisR1.PoolL_PhysicalClose
open Aeneas Aeneas.Std Result PoolL_Physical

theorem excluded (s : Snapshot) (key owner : Key) (refund : Account) (size : Usize)
    (cp : Occupied s key) (plan : size.val = 10000 ∨ size.val = 8504) :
    PoolL_CloseSource.closePrefix (readLength s) (observe s key) refund owner size =
      ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) := by
  exact PoolL_CloseReject.occupied _ _ _ _ _ (Slice.len (bytes s key)) cp plan rfl
#print axioms excluded
end AspisR1.PoolL_PhysicalClose
