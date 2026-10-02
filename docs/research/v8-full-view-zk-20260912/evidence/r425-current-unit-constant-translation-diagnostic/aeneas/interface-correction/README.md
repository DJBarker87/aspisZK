# R425 evaluator interface correction

The earlier `eval-context-inventory.md` proposed calling `InterpExpressions.eval_operand_no_reorganize` directly. That function is private: it appears in `InterpExpressions.ml` but is not declared in the actual R425 `InterpExpressions.mli`. R425 fixture build v1 retained an unbound-value failure for that call. Keep that earlier report as the historical proposal; this receipt supersedes its direct-call API recommendation.

The pinned candidate interface exports `eval_operand` and `eval_operands`. For a constant input, use the documented list API:

```ocaml
let values, ctx_out, continue =
  InterpExpressions.eval_operands config span [ Constant charon_unit ] ctx
in
check (values = [ expected_unit]);
check (ctx_out == ctx);
check (continue witness == witness)
```

The implementation's `prepare_eval_operand_reorganize` returns `(ctx, fun e -> e)` for `Constant _` (source lines 378–379 in the pinned candidate); `eval_operands` prepares once, then evaluates operands into a `tvalue list` (lines 628–640). For a one-element constant list, expected value is a singleton list containing the exact runtime unit value. The context and continuation checks can use physical identity as recorded above. For the malformed valid one-element tuple constant, call the same public `eval_operands` API and compare its `Errors.CFailure` message to the preserved fallback message.

The full interface is copied to `InterpExpressions.mli` here. Its SHA-256 `f0a15cdb3a491148f9bad38077c9c5126411fb5ea4502e38ba1bcb44153371e1` matches the live candidate file. The implementation source SHA-256 is `a686db5af43c4463b357e066330a21f01287bafe0cc2c13394b4b2b4f458f190`; the exact `eval_operands` excerpt is preserved in `InterpExpressions.ml.eval-operands-580-655.txt`. The `Constant _` no-op preparation branch excerpt/hash is in `prepare-operands-source-and-hash.txt`.

This is an interface/call-shape correction only. No source was edited and no build or test was run for this inventory.
