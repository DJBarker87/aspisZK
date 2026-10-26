import PoolL_ProgramControl
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_ProgramAccepted
open Aeneas Aeneas.Std Result PoolL_ProgramSource PoolL_ProgramControl
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
local instance : DecidableEq Key := Classical.decEq _
theorem accepted (a : Account) (id : Key) (w : Bool) :
    require_program_account a id w = ok (.Ok ()) ↔ a.owner = id ∧ a.executable = false ∧ a.is_writable = w := by
  rw [control]
  by_cases ho : a.owner = id <;> cases he : a.executable <;> cases hw : a.is_writable <;> cases w <;> simp [ho]
#print axioms accepted
end AspisR1.PoolL_ProgramAccepted
end
