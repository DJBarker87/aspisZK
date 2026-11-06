import PCB_VaultRef.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCB_VaultLaw

theorem result (h : PCB_VaultRef.PoolV1PairForestTerminalBumpHintsV1) :
    PCB_VaultRef.reference h = ok
      {vault_authority := h.vault_authority, vault_token_account := h.vault_token_account} := by
  rfl

#print axioms result
end PCB_VaultLaw
