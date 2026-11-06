import PCC_RuntimeCpiAccountView
set_option autoImplicit false
namespace PCC
open PCA
/-- SUPPORT only: native builder cuts must discharge metasFromInfos at the
actual instruction. Exclusion from infos is never substituted for exclusion
from M without this fact. No counter or AccountInfo header frame is added. -/
theorem protected_from_infos (before after : PCA_State) (instruction : Instruction)
    (infos : List Nat) (calleeFinal : Bytes → AccountView)
    (runtime : RuntimeCpiAccountView before after instruction infos calleeFinal)
    (a : Nat) (bound : a < before.accountCount)
    (metasFromInfos : ∀ m ∈ instruction.metas, ∃ i ∈ infos,
      (before.loans.state.accounts i).key = m.key.toList)
    (different : ∀ i ∈ infos,
      (before.loans.state.accounts a).key ≠ (before.loans.state.accounts i).key) :
    view after a = view before a := by
  apply runtime.unmentioned a bound
  intro m hm
  obtain ⟨i,hi,hkey⟩ := metasFromInfos m hm
  rw [← hkey]
  exact different i hi
#print axioms protected_from_infos
end PCC
