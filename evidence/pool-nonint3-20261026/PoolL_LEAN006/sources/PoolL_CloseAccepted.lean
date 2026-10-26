import PoolL_CloseControl
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_CloseAccepted
open Aeneas Aeneas.Std Result PoolL_CloseSource PoolL_CloseControl
local instance : DecidableEq Key := Classical.decEq _

/-- Acceptance forces exact length and separation of both close/refund roles. -/
theorem accepted (length : Account → Result Usize) (a refund : Account)
    (owner : Key) (size : Usize) :
    closePrefix length a refund owner size = ok (.Ok ()) ↔
      a.owner = owner ∧ a.executable = false ∧ a.is_signer = false ∧
      a.is_writable = true ∧ refund.key ≠ a.key ∧ refund.is_writable = true ∧
      length a = ok size := by
  rw [control]
  classical
  by_cases ho : a.owner = owner <;> by_cases hk : refund.key = a.key <;>
    cases he : a.executable <;> cases hs : a.is_signer <;>
    cases hw : a.is_writable <;> cases hr : refund.is_writable <;>
    cases hl : length a <;> simp [ho,hk,he,hs,hw,hr] <;> scalar_tac

#print axioms accepted
end AspisR1.PoolL_CloseAccepted
end
