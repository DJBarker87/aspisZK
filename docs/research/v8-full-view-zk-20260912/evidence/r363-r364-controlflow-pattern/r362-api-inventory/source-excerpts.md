# Source excerpts (line numbers from pinned sources)

## R349 `src/PrePasses.ml` (SHA-256 `09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd`), lines 940–981

```ocaml
940 let lower_nested_loop_returns (crate : crate) (f : fun_decl) : fun_decl =
941   match f.body with
...
952       if not has_nested_return then f
953       else
954         let option_ids =
955           TypeDeclId.Map.fold
956             (fun id (decl : type_decl) ids ->
957               if decl.item_meta.lang_item = Some "Option" then id :: ids
958               else ids)
959             crate.type_decls []
960         in
961         let option_id =
962           match option_ids with
963           | [ id ] -> id
964           | _ ->
965               [%craise] f.item_meta.span
966                 "Nested-loop returns require exactly one Option language item"
967         in
...
980             id = TAdtId option_id;
981             generics = TypesUtils.mk_generic_args [] [ return_ty ] [] [];
```

`apply_passes` list at `PrePasses.ml:3559`: `("lower_nested_loop_returns", lower_nested_loop_returns);`.

## Generated Charon types

`charon-ml/src/generated/Generated_Types.ml`, SHA-256 `6e977831c8fb7a3e1b6b77e1b98e5cc71de8841186f98c5de5fd68c93fdb9794`:

- `:499–504`: `generic_args` record has `regions`, `types`, `const_generics`, `trait_refs` lists.
- `:507–518`: `generic_params` record has `regions`, `types`, `const_generics`, `trait_clauses`, `regions_outlive`, `types_outlive`, and `trait_type_constraints`.
- `:758`: `TVar of type_var_id de_bruijn_var`.
- `:835–841`: `type_param = { index : type_var_id; name : string }`.
- `:969–991`: `item_meta` fields include `name`, `span`, source text, attributes/visibility, `is_local`, `opacity`, and `lang_item`.
- `:1036–1058`: `item_source` begins with `TopLevelItem`, closure, trait-declaration, and trait-implementation cases.
- `:1221–1235`: `type_decl = { def_id; item_meta; generics; src; kind; layout; ptr_metadata }`.
- `:1237–1249`: `type_decl_kind` has `Struct`, `Enum`, `Union`, `Opaque`, `Alias`, `TDeclError`.
- `:1259–1270`: `variant = { id; span; attr_info; variant_name; fields; discriminant }`.
- `:1154–1164`: name path element `PeInstantiated of generic_args binder`; comment says empty binder parameters denote monomorphization.

`charon-ml/src/Types.ml`, SHA-256 `129d035a066ecd15215b266fecd66420e11505d1ac87c907976ba183e2b6c1eb`, lines 13–15 instantiate separate `IdGen` modules for `TypeVarId`, `TypeDeclId`, and `VariantId`. `charon-ml/src/Identifiers.ml`, SHA-256 `f6783965202454424e1441b0013e1e666273a9278d864cfdba4a02c951b4798b`, signature lines 79–83 and implementation lines 218–260 expose zero/generator helpers, stateful generator functions, `fresh`, `to_int`, and `of_int`. `TypeDeclId.Map` is a map module with standard `add` in its `Collections.Map` interface (Identifiers.ml lines 47–75).

`charon-ml/src/generated/Generated_FullAst.ml`, SHA-256 `ff1d134a373dd18d2327574f9f7033749b4e0f17088824531f67f32f6aa86292`: lines 237–247 define `declaration_group` including `TypeGroup`; lines 268–270 define `NonRecGroup of 'a0` and `RecGroup of 'a0 list`.
`charon-ml/src/GAst.ml`, SHA-256 `d5f5407492e54151cbc687b273c93b2d988b778751f5c208945d968f7eb428bb`: lines 32–46 define the crate record with `declarations` and `type_decls` fields.
`charon-ml/src/TypesUtils.ml`, SHA-256 `56363aecefc1b22d212f5d0e4a035ba38d965e3761422fe2d5d0fe7312ad909c`.

## Exact linked-source-candidate NameMatcher

Pinned `charon-ml/src/NameMatcher.ml`, SHA-256 `a6aac1d07e356b864a9146723e31401ff26be569ce2ac71d7410bc14d1bb5061`. The installed R349 image package path `/home/opam/.opam/5.2/lib/charon/NameMatcher.ml` reports the same SHA-256. This is compared source identity and package-path evidence, not a direct inspection of linked object contents.

- `:459–486`: `instantiate_name_generics`; special handling when binder params are empty, preserving late-bound regions in the returned argument record; otherwise checks generic arities and substitutes binder args.
- `:488–500`: `match_name_with_generics` handles final `PeInstantiated binder`, calls `instantiate_name_generics binder g`, strips the suffix, then matches.
- `:895–898`: `type_var_to_pattern` looks up the variable ID in the computed type-variable constraints map.
- `:931–945`: `compute_constraints_map` maps each declaration type parameter index to `Some (VarName x.name)`.
- `:985–1015`: `name_with_generic_args_to_pattern_aux` recurses over path elements; a `PeInstantiated _` arm returns `[]` (102–1055 in zero-based prose: file lines 1012–1015).
- `:1037–1053`: `ty_to_pattern_aux` recursively converts an ADT's generic arguments, looks up the type declaration, converts its name with those generics, and maps `TVar v` through `type_var_to_pattern`.
- `:1145–1160`: `generic_args_to_pattern` maps regions, types and const generics, concatenating region/type/const patterns.
- `:1162–1175`: `name_to_pattern` constructs a pattern and asserts a match unless `TkName`.
- `:1177–1195` (continues to line 1199): `name_with_generics_to_pattern` builds a constraints map from supplied declaration params, converts args, calls the name conversion helper, and asserts a match unless `TkName`.

## Source notes about candidate API use

The inspected R349 `PrePasses.ml` and Charon source search found no example of a prepass constructing/inserting a new `type_decl` with a fresh `TypeDeclId` into both crate maps and ordered `declarations`. The records, constructors, and ID functions listed above are declarations/API pieces only. This is an inventory of available source forms, not an assembled creation recipe.
