let name_to_pattern (ctx : ctx) (c : to_pat_config) (n : T.name) : pattern =
  (* Convert the name to a pattern *)
  let pat = name_to_pattern_aux ctx c n in
  (* Sanity check: the name should match the pattern *)
  assert (
    c.tgt = TkName
    || match_name ctx
         {
           map_vars_to_vars = true;
           match_with_trait_decl_refs = c.use_trait_decl_refs;
         }
         pat n);
  (* Return *)
  pat

(** We use the [params] to compute proper names for the variables. Note that it
    is safe to provide empty generic parameters. *)
let name_with_generics_to_pattern (ctx : ctx) (c : to_pat_config)
    (params : T.generic_params) (n : T.name) (args : T.generic_args) : pattern =
  (* Convert the name to a pattern *)
  let pat =
    let m = compute_constraints_map params in
    let args = generic_args_to_pattern ctx c m args in
    name_with_generic_args_to_pattern_aux ctx c n (Some args)
  in
  (* Sanity check: the name should match the pattern *)
  assert (
    c.tgt = TkName
    || match_name_with_generics ctx
         {
           map_vars_to_vars = true;
           match_with_trait_decl_refs = c.use_trait_decl_refs;
         }
         pat n args);
  (* Return *)
  pat
