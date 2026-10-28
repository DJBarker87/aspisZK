import NDO_JFu_DigestDecode
set_option autoImplicit false
namespace AspisR1.JFu_ResultBranch
open Aeneas Aeneas.Std Result

theorem value {T E : Type} (r : core.result.Result T E) (v : T)
    (branch : core.result.Result.Insts.CoreOpsTry.branch r=ok (.Continue v)) : r=.Ok v := by
  cases r <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch]

#print axioms value
end AspisR1.JFu_ResultBranch
