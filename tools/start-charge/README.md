# Transcript start-charge packet

The proofs are additive modules in
`docs/research/100bit-spend-path-20261013/lean/`.

Dependency order:

1. `StartChargePrefix`
2. `StartChargeHit`
3. `StartChargeCompletion`
4. `StartChargeClean`
5. `StartChargeProbability`
6. `StartChargeNumeric`
7. `OraclePortHeadlineFrozenPerAttempt`

For a changed module or identified changed dependency environment:

```sh
python3 -B tools/start-charge/compile.py MODULE
```

The launcher uses the accepted integrated port command's environment, with
`/tmp/codex-cx-start-charge-20261021-objects` prepended. It compiles one
module, under the shared mkdir lock, with Lean 4.32.0, `-j1 -M4400
-DElab.async=false`, and `/usr/bin/time -l`. It refuses unchanged
source/dependency retries and preserves failed attempts. It does not build
dependencies or modify shared objects.

Audit the finished packet without recompiling:

```sh
python3 -B tools/start-charge/audit.py
```

The audit checks the exact premise signature, source/receipt agreement,
every new theorem's standard-axiom report, final environment, direct import
object hashes, all 119 reused integrated port source/object pins, and the
absence of shipped or existing Lean source changes. The premise comparison
normalizes only the theorem name by extracting its argument block; the
conclusion intentionally improves the coefficient and removes the positive
lower query bound. This is not a claim that source correspondence has been
discharged.

All receipts are under
`docs/research/100bit-spend-path-20261013/evidence/start-charge-20261021/`.
Historical object discrepancies are retained in `cache-equivalence.json`;
the final pass uses the integrated environment. No object or binary belongs
in the repository. Unchanged frozen dependencies reuse accepted evidence;
this packet does not claim a new source-to-deployed release rebuild.
