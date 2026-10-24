import S1PrepareBudgetCoreV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedBudget
open Aeneas Aeneas.Std Result PreparedHashCode
example {H : Type} (D : aspis_core.Digest32 H) (hash : H) (parts : Slice (Slice U8)) :
    bounded 3 (do let a ← effects.digest D hash parts; pure a) := by
  apply then_bound (cost:=1)
  · omega
  · exact digest_bound D hash parts
  · intro x
    exact pure_bound _ x
end AspisR1PublicPreparation.PreparedBudget
