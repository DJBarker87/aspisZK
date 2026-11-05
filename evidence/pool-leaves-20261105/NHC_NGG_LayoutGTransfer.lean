import Lean
import NHC_NGG_LayoutDefs

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NHC_NGG_LayoutGTransfer
open NHC_NGG_SpineRef NHC_NGG_LayoutValue
theorem result (n : Usize) (unique : core.result.Result Unit NGGSpineError) :
    NHC_NGG_SpineRef.layout_tail 4#usize false n unique =
      ok (value false false n unique) := by
  have a1 : Usize.wrapping_add 4#usize 1#usize = 5#usize := NHC_NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a2 : Usize.wrapping_add 4#usize 2#usize = 6#usize := NHC_NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a3 : Usize.wrapping_add 4#usize 3#usize = 7#usize := NHC_NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a5 : Usize.wrapping_add 4#usize 5#usize = 9#usize := NHC_NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a6 : Usize.wrapping_add 4#usize 6#usize = 10#usize := NHC_NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a7 : Usize.wrapping_add 4#usize 7#usize = 11#usize := NHC_NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have ck : Usize.checked_add 11#usize 0#usize = some 11#usize := NHC_NGG_Scalar.checked_add _ _ _ (by rfl)
  have last : Usize.wrapping_add 11#usize 1#usize = 12#usize := NHC_NGG_Scalar.wrapping_add _ _ _ (by rfl)
  cases unique <;>
    simp only [NHC_NGG_SpineRef.layout_tail,cursor,expected,fields,value,lift,bind_tc_ok,
      Bool.false_eq_true,ite_false,ite_true,
      NHC_NGG_SpineRef.core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame,a1,a2,a3,a5,a6,a7,ck,last] <;>
    split_ifs <;> rfl
#print axioms result
end NHC_NGG_LayoutGTransfer

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
