(* Task-scoped, opt-in Lean model metadata. The concrete models are checked
   definitions consuming exact extracted methods, never axiom templates. *)
let lean_builtin_types =
  if Sys.getenv_opt "AENEAS_R1_TRY_GRAPH" = Some "1" then
    mk_type "core::ops::try_trait::NeverShortCircuitResidual"
      "AspisR1CuArraySource.core.ops.try_trait.NeverShortCircuitResidual"
      ~kind:(KEnum []) :: lean_builtin_types
  else lean_builtin_types

let lean_builtin_trait_impls =
  if Sys.getenv_opt "AENEAS_R1_TRY_GRAPH" = Some "1" then
    [
      mk_trait_impl
        "core::ops::try_trait::Try<core::ops::try_trait::NeverShortCircuit<@T>>"
        "AspisR1.CuSavingsTryGraphRuntime.neverTry";
      mk_trait_impl
        "core::ops::try_trait::Residual<core::ops::try_trait::NeverShortCircuitResidual, @T, core::ops::try_trait::NeverShortCircuit<@T>>"
        "AspisR1.CuSavingsTryGraphRuntime.neverResidual";
    ] @ lean_builtin_trait_impls
  else lean_builtin_trait_impls
