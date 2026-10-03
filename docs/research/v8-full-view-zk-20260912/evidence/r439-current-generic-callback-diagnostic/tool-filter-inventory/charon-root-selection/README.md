# Charon root-selection preflight for R438 Fun284

Read-only inspection of Charon commit `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`, the exact source commit recorded for the R438 capture. Full pinned copies of the relevant options, parser, resolver, root registration, and nameable-child implementation are in `pinned-charon/`. Hashes and relevant ranges are in `source-pins.json`.

## Finding

Charon's supported `--start-from` option restricts extraction to a selected call graph, but its supported root resolver does not provide a precise direct root for this synthetic closure method:

- The R438 source inventory records the target as the unique Function 112 descriptor: closure `#2`'s `call_mut`, from the closure FnMut implementation (TraitImpl 35, FnMut trait 3, method 0). Its actual call node is in `Iterator::fold` (Function 70).
- `Pattern` identifiers are parsed from alphanumeric characters and `_` only (`name_matcher/parser.rs:80–101`). The synthetic `closure#2` spelling uses `#`, which is not representable as one identifier in this grammar.
- The path resolver follows later path components only through `FullDef::nameable_children` (`resolve_path.rs:148–168`). `FullDef::nameable_children` has cases for modules, enum variants, inherent impls, traits, trait impls, and inherent associated items; it has no closure case (`full_def.rs:1183–1220`).
- `--start-from` can begin with an impl pattern. For trait impl patterns, the resolver accepts the pattern only when the self type resolves to a named ADT; it filters candidate impls by `ty::Adt` (`resolve_path.rs:100–145`, especially 114–132 and 136–145). A synthetic closure type is not a named ADT under that check. The grammar supports `_` wildcard types; a wildcard self type takes the resolver branch that collects all impls for the trait, so it is not a single-closure selector (`parser.rs:104–135`, `resolve_path.rs:108–133`).
- The root loop enqueues IDs returned by `resolve_path` (`translate_crate.rs:965–974`). `base_kind_for_item` maps ordinary function and trait-impl IDs to translation kinds but explicitly rejects `DefKind::Closure` as a non-top-level kind (`translate_crate.rs:232–270`). Translating a normal function also visits nested HIR items in its body and enqueues them (`translate_items.rs:79–98`), which is different from directly naming only the closure method.

These are source facts about supported path parsing and root registration. No guessed selector was run. The inspection does not decide whether an alternate extraction mode can preserve the closure's borrowed return, does not edit/projection-prune LLBC, and makes no execution, dispatch, or proof claim.

## Relevant source locations

- `options.rs:65–120`: `start_from` documented as a call-graph root selector.
- `resolve_path.rs:64–183`: path resolution; trait impl matching and named-ADT restriction.
- `name_pattern_parser.rs:72–137`: identifier and impl-pattern grammar; wildcard syntax.
- `name_matcher_mod.rs:10–40`: `PatElem` representation (`Ident` stores only a string, with no disambiguator field).
- `full_def.rs:1183–1220`: nameable children exposed to path traversal.
- `translate_crate.rs:220–271, 274–302, 965–974`: path dispatch, accepted registration kinds, root enqueueing.
- `translate_items.rs:79–98`: nested-item enqueueing while processing a function body.

The captured R438 input and selected descriptor inventory remain the primary record for the target's identity: `../root-launch-a/saved-output/R438GenericClosureDispatch.llbc` and `../inventory/selector-inventory.json`.
