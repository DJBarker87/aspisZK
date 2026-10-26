import PoolM_Source
set_option autoImplicit false
namespace PoolM_CancelGuard
open Aeneas Aeneas.Std Result PoolM_Owned

/-- Exact accepted metadata of the extracted prepared-plan reference. -/
theorem prepared_ok (a : Account) (size : Usize) :
    prepared a size = ok 0#u32 ↔
    a.owner_matches = true ∧ a.executable = false ∧ a.signer = false ∧
      a.writable = true ∧ a.len = size := by
  cases ho : a.owner_matches <;> cases he : a.executable <;>
    cases hs : a.signer <;> cases hw : a.writable <;>
    simp [prepared, ho, he, hs, hw, bne_iff_ne] <;> scalar_tac

/-- Size mismatch preserves the exact InvalidAccountData encoding, regardless
of which earlier metadata arm rejects. No suffix is executed. -/
theorem prepared_wrong_size (a : Account) (size : Usize) (h : a.len ≠ size) :
    prepared a size = ok 1#u32 := by
  cases ho : a.owner_matches <;> cases he : a.executable <;>
    cases hs : a.signer <;> cases hw : a.writable <;>
    simp [prepared, ho, he, hs, hw, h]

/-- The authority role requires System ownership before any plan borrow. -/
theorem authority_ok (a : Account) : authority a = ok 0#u32 ↔
    a.signer = true ∧ a.writable = true ∧ a.executable = false ∧
      a.system_owned = true := by
  cases hs : a.signer <;> cases hw : a.writable <;>
    cases he : a.executable <;> cases ho : a.system_owned <;>
    simp [authority,hs,hw,he,ho]

theorem authority_foreign (a : Account) (h : a.system_owned = false) :
    authority a = ok 2#u32 := by
  cases hs : a.signer <;> cases hw : a.writable <;>
    cases he : a.executable <;> simp [authority,hs,hw,he,h]

#print axioms prepared_ok
#print axioms prepared_wrong_size
#print axioms authority_ok
#print axioms authority_foreign
end PoolM_CancelGuard
