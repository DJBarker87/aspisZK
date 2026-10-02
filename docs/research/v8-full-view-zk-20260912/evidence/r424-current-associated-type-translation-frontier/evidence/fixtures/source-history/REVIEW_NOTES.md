# R424 fixture/API review notes

- Candidate module was not edited: SHA256 `48336b273fafc9fec71686f15896976cddf1a41367a5556749af0f13437ef4cf`.
- R396 input hash: `399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae`.
- `make_subst_from_generics` uses the exact wrapper arguments `__FILE__`, `__LINE__`, `None`, params, args, and self.
- The malformed-arity case first makes a valid impl reference, then changes only the impl-kind generic list before calling `normalize_ty`; it reaches the candidate's substitution path rather than failing while constructing the fixture.
- Config is set to `fail_hard := false`. Guard failures require `Errors.CFailure` with the exact expected R424 message. Malformed arity accepts only Aeneas `CFailure` from its native argument-count wrapper.
- The lifetime fixtures are separate: a `TRef` with a `Free` region; then a function pointer under an outer region binder with inner `Bound(0)` and ambient `Bound(1)`. For the latter, the fixture's exact-shape constructor lifts only the ambient region to `Bound(2)` in the trait-declaration reference's stored empty region binder; it preserves the associated argument and checks the resulting projection inside the outer function pointer. This helper is test-only, not a production rewrite or general de Bruijn lemma.
- The recursive projection fixture is expected to reject at `require_no_source_binders` through the nested trait-ref region binder; it does not test the separate cycle-stack guard.
- Source inspection confirmed constructors for `TUInt U32`, `TLiteral TBool`, `TTuple`, `TRef`, `TFnPtr`, `fun_sig`, `region_param`, and `de_bruijn_id = int`; it also confirmed `LlbcOfJson.crate_of_json_file`. R396's saved decoded census confirms Try trait 11, impl 24, Output type item 0, impl generics B/C, Output source `Free(1)`, empty associated binder, and Try self type `ControlFlow<B,C>`.
- Still unchecked until the lead's run: generated id-map `Core.Map.set` call form, wrapped `Aeneas` module visibility in the fixture executable, and direct Dune byte-object target spelling. No candidate behavior was changed to address these draft-level points.
- The first uncompiled fixture was edited in place before a byte snapshot. `history/initial-v1-preservation-note.md` records known issues but exact original bytes/hash are unavailable; it is not represented as an exact archive.

The Dune integration and runner are plans only. No fixture compile or execution occurred. The fixture is finite, targeted evidence only; it is not broad GAT coverage, universal substitution correctness, compiler preservation, Rust source correspondence, translation success, or a security result.
