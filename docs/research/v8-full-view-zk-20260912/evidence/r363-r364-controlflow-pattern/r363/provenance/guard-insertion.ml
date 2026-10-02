  match List.rev n, generics with
  | T.PeInstantiated binder :: reversed_prefix, (None | Some [])
    when binder.binder_params = TypesUtils.empty_generic_params ->
      let m = compute_constraints_map binder.binder_params in
      let instantiated_args =
        generic_args_to_pattern ctx c m binder.binder_value
      in
      name_with_generic_args_to_pattern_aux ctx c (List.rev reversed_prefix)
        (Some instantiated_args)
  | _ ->
  match n with
