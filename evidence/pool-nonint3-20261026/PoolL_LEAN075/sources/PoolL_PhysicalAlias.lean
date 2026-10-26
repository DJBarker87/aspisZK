import PoolL_Physical
set_option autoImplicit false
namespace AspisR1.PoolL_PhysicalAlias
open Aeneas Aeneas.Std Result PoolL_Physical

theorem length_alias (s : Snapshot) (a b : Account) (same : a.key = b.key) :
    readLength s a = readLength s b := by simp only [readLength,same]
theorem empty_alias (s : Snapshot) (a b : Account) (same : a.key = b.key) :
    readEmpty s a = readEmpty s b := by simp only [readEmpty,same]
theorem observe_alias (s : Snapshot) (a b : Key) (same : a = b) :
    observe s a = observe s b ∧ bytes s a = bytes s b := by subst b; exact ⟨rfl,rfl⟩
#print axioms length_alias
#print axioms empty_alias
#print axioms observe_alias
end AspisR1.PoolL_PhysicalAlias
