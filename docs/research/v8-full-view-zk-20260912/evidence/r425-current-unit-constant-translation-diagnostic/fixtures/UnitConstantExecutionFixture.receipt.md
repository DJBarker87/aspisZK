# R425 direct interpreter execution fixture draft

This is a separate, uncompiled fixture. It leaves `UnitConstantFixture.draft.ml` unchanged. It reads the R419 candidate using `LlbcOfJson.crate_of_json_file`, takes function 58's decoded source span, computes `Interp.compute_contexts crate`, and constructs the minimal evaluator context with `InterpUtils.initialize_eval_ctx (Some span) decls_ctx [] [] [] ContextsBase.empty_marked_ids`.

For each of `ConcreteMode` and `SymbolicMode`, it calls the candidate's actual `InterpExpressions.eval_operand_no_reorganize` with Charon's exact `ExpressionsUtils.mk_unit_const`. It asserts (1) exact zero-field `VAdt` plus unit type, (2) physical context identity, (3) physical identity of an allocated payload-bearing symbolic expression after applying the returned continuation, and (4) unchanged `Errors.CFailure` diagnostic for `CAdt(None,[unit])` with its valid one-element tuple type. The two modes total eight counted checks. There is no count guard; expected marker is `R425 unit execution checks passed: 8`.

This is finite integration coverage for the two current modes and those two inputs. It is not universal evaluator correctness, callback execution, or a source-semantics proof. No fixture build or run has occurred.

Source/API basis and hashes are in `../aeneas/eval-context-inventory.md` and its JSON. The R419 input SHA is `7f82eaabe855e89d735b21f9af5f6a983abea6b2f4d93d4b8bae747abd2829e2`; exact unit node provenance is in `../llbc/R419-unit-constant.json`.
