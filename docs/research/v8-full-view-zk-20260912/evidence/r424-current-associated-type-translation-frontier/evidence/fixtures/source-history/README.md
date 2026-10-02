# R424 focused fixture draft

`ConcreteAssociatedTypesFixture.draft.ml` is a typed OCaml fixture draft that reads the exact saved R396 JSON LLBC with `LlbcOfJson.crate_of_json_file`, takes actual Try impl row 24 / Output associated item row 0, and builds the focused projection records using the pinned substitution API. It covers:

- actual impl24 `Output(unit, unit) = unit`;
- distinct symbolic `B` and `C`, requiring the result equal `C`;
- a borrowed `C` with a free lifetime, requiring structural preservation;
- an inner function-pointer binder with local `Bound(0)` and ambient outer `Bound(1)`, inserted beneath an outer function-pointer binder; the fixture constructs the corresponding `trait_decl_ref` representation with ambient `Bound(1)` lifted to `Bound(2)` under its stored empty region binder, then requires normalized output preserve the expected inner arrow;
- a `Clause` projection remaining unchanged;
- rejection for mismatched trait identity, missing associated type, malformed impl argument arity, nonempty associated binder, recursive source projection, and missing impl entry.

The arrow lift is deliberately fixture-local and shape-specific. It only changes `Bound(1)` to `Bound(2)` in the two reference positions of the test arrow while preserving its inner `Bound(0)`. It is not a proposed production transformer or a generic binder correctness result. The recursive source-projection case reaches the candidate's explicit nested-region-binder guard through the embedded `TTraitType`; it does **not** establish that the candidate's recursion-stack detector is exercised.

The fixture mutates copied immutable map values only; it does not change the serialized fixture or candidate module. Negative checks accept only the pinned candidate's `Errors.CFailure`, ordinary `Failure` (used when fail-hard is active), or `Invalid_argument` (native malformed-arity failure), and fail if normalization returns normally. This avoids swallowing arbitrary test bugs.

Pinned source/API confirmation from the read-only R385 package image: `TUInt U32`, `TLiteral TBool`, `TTuple`, `TRef`, `TFnPtr`, `fun_sig` fields, `region_param` fields, and integer de Bruijn levels are present in Charon's generated types; `OfJson.crate_of_json_file` exists; Aeneas `Substitute.make_subst_from_generics` takes `file`, `line`, `span`, params, args, and self. The fixture uses `Core.Map.set` for the generated id-map aliases and module paths through the wrapped `Aeneas` library. Those final map/wrapped-Dune typing details have not been compiled.

`dune-integration.draft` proposes adding the helper module to the fresh candidate's explicit `aeneas` module list and one dedicated fixture `test` stanza. `runner-plan.json` records staged commands and inherited caps. They are not executed. The object-target spelling is inferred from cached object paths and remains unvalidated. There is no existing test stanza in the pinned source tree.

The input R396 LLBC JSON SHA256 is `399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae`. The candidate helper draft SHA256 is `48336b273fafc9fec71686f15896976cddf1a41367a5556749af0f13437ef4cf`, matching the helper root compiled separately by the lead. No fixture compilation or execution has occurred.

This is fixture preparation only. It is not broad GAT coverage and does not prove universal binder/substitution correctness, compiler preservation, Rust source behavior, translation success, or any security property.
