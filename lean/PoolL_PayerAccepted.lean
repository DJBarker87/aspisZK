import PoolL_PayerControl
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_PayerAccepted
open Aeneas Aeneas.Std Result PoolL_AllocateSource PoolL_PayerControl
local instance : DecidableEq Key := Classical.decEq _

theorem accepted (system loader : Key) (payer sys : Account) :
    payerSystem system loader payer sys = ok (.Ok ()) ↔
      payer.is_signer = true ∧ payer.is_writable = true ∧ payer.executable = false ∧
      payer.owner = system ∧ sys.key = system ∧ sys.owner = loader ∧
      sys.executable = true ∧ sys.is_signer = false ∧ sys.is_writable = false := by
  rw [control]
  simp only [ite_eq_left_iff,ite_eq_right_iff]
  cases hs : payer.is_signer <;> cases hw : payer.is_writable <;>
    cases he : payer.executable <;> cases se : sys.executable <;>
    cases ss : sys.is_signer <;> cases sw : sys.is_writable <;>
    by_cases hp : payer.owner = system <;> by_cases hk : sys.key = system <;>
    by_cases hl : sys.owner = loader <;> simp [hp,hk,hl,hs,hw,he,se,ss,sw]

#print axioms accepted
end AspisR1.PoolL_PayerAccepted
end
