import R1Z.PV_RDCD_Option194
import R1Z.PV_CB_Op107Funs
set_option autoImplicit false
namespace R1Z.PV_RDCD_OptionBinding
open Aeneas Aeneas.Std Result
open PV_RDCD_Option194
/-- Every payload, not a finite test: deployed branch and retained extraction coincide. -/
theorem branch (T : Type) (o : Option T) :
    PV_CB_ShippedOp107.core.option.Option.Insts.CoreOpsTry_traitTry.branch o =
    PV_RDCD_Option194.branch o := by cases o <;> rfl
/-- The empty residual payload rules out the assertion's failing path. -/
theorem residual (T : Type) (o : Option core.convert.Infallible) :
    PV_CB_ShippedOp107.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual T o =
    fromResidual T o := by
  cases o with
  | none => simp [PV_CB_ShippedOp107.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      read_discriminant, R1Z.PV_CB_OptionDiscriminant.optionDiscriminant, fromResidual]
  | some impossible => exact nomatch impossible
#print axioms branch
#print axioms residual
end R1Z.PV_RDCD_OptionBinding
