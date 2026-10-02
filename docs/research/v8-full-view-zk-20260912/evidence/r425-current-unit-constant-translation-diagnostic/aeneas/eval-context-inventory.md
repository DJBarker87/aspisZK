# R425 direct evaluator context construction inventory

Read-only notes for how a native fixture can call pinned `InterpExpressions.eval_operand_no_reorganize` on the unit constant. No build or execution occurred.

## Pinned construction path

- Parse the captured R419 LLBC with the existing `LlbcOfJson.crate_of_json_file`; use function ID 58 and its `item_meta.span` as the exact source span. The saved LLBC unit node is under function 58 at `.../Ref/ptr_metadata`; the leaf itself is a `constant_expr`, so invoke the evaluator with `Constant cv`.
- Build declaration/interpreter contexts with `Interp.compute_contexts crate`. This is the existing interpreter entry used for unit-function testing.
- Use `InterpUtils.initialize_eval_ctx (Some span) decls_ctx [] [] [] ContextsBase.empty_marked_ids`. These empty lists are region groups, type parameters, and const-generic parameters. The initializer creates all fresh-ID functions and a const-generic map (empty here); the initial environment is `[EFrame]`, and ended regions are empty. This avoids manually fabricating the context record.
- For concrete and symbolic mode separately use `Contexts.mk_config Contexts.ConcreteMode` and `Contexts.mk_config Contexts.SymbolicMode`. The evaluator takes the config, the exact `Meta.span`, `Constant cv`, and the initialized context.

The pinned `Interp.Test.test_unit_function` uses the same constructor pattern: `initialize_eval_ctx (Some span) decls_ctx [] [] [] empty_marked_ids`, with `decls_ctx` computed from the crate, then `mk_config ConcreteMode`. This is the nearest in-tree precedent.

## Identity and fallback observations

The exact unit helper result in `InterpExpressions.draft.diff` is `(v, ctx, fun e -> e)`. A fixture can test physical context identity with `ctx_out == ctx_in`. For continuation identity, compare the returned continuation applied to a freshly allocated witness expression: `cc witness == witness`. `SymbolicAst.Panic` alone is a nullary immediate constructor; a payload-bearing constructor such as `SymbolicAst.Assertion (ctx, true, expected_tvalue, SymbolicAst.Panic)` gives a non-immediate identity witness. This tests that the result is the original expression object, not just structural equality.

For a malformed constant that the helper returns as `None`, the integration candidate retains the old fallback verbatim. Set `Config.fail_hard := false`, call the evaluator, catch `Errors.CFailure`, and compare `failure.msg` with `"Found unexpected constant: " ^ InterpUtils.constant_expr_to_string ctx malformed`. Do not treat successful return or a different message as an expected rejection. The call should use the same original `ctx` and span so the diagnostic is exactly comparable.

The existing runtime unit value precedent is `ValuesUtils.mk_unit_value = { value = VAdt { variant_id = None; fields = [] }; ty = mk_unit_ty }`, matching the candidate helper representation.

## Source hashes and excerpts

- `interp/InterpExpressions.ml` SHA-256 `531b0ee1c6d26d463d07c6e1dbdc75a7cce32cf970adcbc59dfafd75bfdd914f`: evaluator signature lines 399–402; original fallback lines 573–575.
- `interp/Interp.ml` SHA-256 `b597a7276d7fd1d6e721f7902ad9f4f03c8281cf581a81521c0ba1031ddba308`: `compute_contexts` begins at line 52; existing unit-function context/config pattern around lines 642–675.
- `interp/InterpUtils.ml` SHA-256 `23c4394d0a7328d590e9092f813a1c372d7ef989d646375db65bb4ec9d5d03e1`: `constant_expr_to_string` alias at line 82 and `initialize_eval_ctx` lines 744–804.
- `llbc/Contexts.ml` SHA-256 `8e6598bc7b5a2104b64de0c14a7f4733a1fc1bddbe1e8596c7b43d1a75eaa600`: `mk_config` lines 21–25; `eval_ctx` record lines 137–164.
- `llbc/ContextsBase.ml` SHA-256 `576ab402b0ff94d8450b9462b8337bc03f054d7cc62ce9485d2e193227e48d6a`: `marked_ids` and `empty_marked_ids` lines 137–166.
- `llbc/Print.ml` SHA-256 `f69722e44a8433508d694d9c9a92ade64aa24e7d3e3f895447af2a40b9bf9b33`: `EvalCtx.constant_expr_to_string` definition at lines 115–117.
- `llbc/ValuesUtils.ml` SHA-256 `ff1f7619b2b33046d64c9e90c98572c821aaef46e786702d5085b945716a9320`: canonical `mk_unit_value` lines 9–10.
- `symbolic/SymbolicAst.ml` SHA-256 `13240e906d72548bd8eb8ee1ae111f7ffc10c7831bb830a5de7e6807c7737c92`: payload-bearing `Assertion` and nullary `Panic` constructors lines 142–185.
- Charon `Generated_Meta.ml` SHA-256 `6347593179d33b25f9c0c0ab05f4b1776e08f3163e8278d06b62504d41feb0a4`: parsed span record definitions; fixture avoids constructing a synthetic span by using the loaded function's source span.

The API/fixture spellings are source-derived but the R425 fixture remains uncompiled and unexecuted. This is construction guidance only, not a claim that callback execution, the entire iterator callback, or translation semantics are established.
