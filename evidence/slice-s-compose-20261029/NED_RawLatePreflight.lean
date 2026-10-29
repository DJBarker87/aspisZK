import NED_LateCarrierFields
set_option autoImplicit false
noncomputable section
namespace NED_RawLatePreflight
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct

theorem option_ne (a b : Option U64) :
    core.cmp.PartialEq.ne.trait_default
      (core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEqU64) a b =
      ok (decide (a ≠ b)) := by
  cases a <;> cases b
  all_goals simp [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    core.option.Option.Insts.CoreCmpPartialEqOption,
    core.option.Option.Insts.CoreCmpPartialEqOption.eq,
    core.cmp.PartialEqU64,core.cmp.impls.PartialEqU64.eq,
    AspisR1AdapterReconstruct.optionDiscriminant_none,
    AspisR1AdapterReconstruct.optionDiscriminant_some]
  all_goals first | rfl | decide | scalar_tac

#print axioms option_ne
end NED_RawLatePreflight
