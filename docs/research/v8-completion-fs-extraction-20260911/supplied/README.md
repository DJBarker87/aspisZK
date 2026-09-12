# Aspis V8 completion pack — first attempts, including Fiat–Shamir

Prepared 11 September 2026. Start with **PROMPT.md**.

This folder is an additive working handoff, not a replacement for your completed
local repair. It contains Lean proof attempts, executable reference code,
regression tests, first-party dependency/build tools and a complete remaining-
obligation map. It does **not** claim all remaining formalisation is solved.

## Validation status

The Python code and tests were run in the authoring environment. New Lean/Lake
and Rust/Cargo compilation were unavailable there. **All new Lean and Rust are
first attempts requiring compilation and repair.** The source inventory checks
for lexical admissions but does not certify theorem meaning or imported code.
Read [results/VALIDATION.json](results/VALIDATION.json) for the exact final test counts and limitations.

The remote repository still exposed `30a303a344dbb42e24ad8f42a8804819747942bc`
when checked. The user's completed local repair was not visible. Run the
read-only reconciliation stage before integration; do not overwrite it.

## Folder map

- `PROMPT.md`: detailed task prompt for the implementation/research agent.
- `lean/AspisV8Completion/`: proposed proof bodies for finite probability,
  adaptive hazards, lazy-oracle cache, first exposures, causal prefixes,
  rejection/distinct samplers, authentication accounting, FS game transport,
  replay, decoder invariants, payment slices, masking and resource arithmetic.
- `aspis_completion/`: executable Python reference algorithms and controls.
- `rust/`: uncompiled dependency-free canonical wire/Merkle/trace controls.
- `integration/`: pinned endpoint inspection and local-repair integration guide.
- `tools/`: read-only repair discovery, source/variant resolution, new build
  roots, axiom inventory and fresh kernel replay.
- `config/`: explicit profile, transcript, security and CU obligations.
- `docs/`: detailed FS, extraction/ZK/CU, proof/status and toolchain guidance.
- `tests/`, `results/`: reproducible checks and actual execution records.
- `reference/`: prior audit as background, not new validation.

## Run the portable code first

From the extracted folder:

```sh
python3 run.py --stage python
python3 run.py --stage static
```

These need only Python3.11+ standard library. They perform no network requests,
Git writes, deployment, account actions or credential access.

Reconcile the real completed local repair:

```sh
python3 run.py --stage preflight --repo /actual/path/to/aspisZK
```

The report identifies candidate changed endpoints and hashes. A name match is
not a proof that a repair is correct; the agent must inspect its producer.

Compile the Lean attempts against an **existing, separately pinned patched**
Mathlib/Lean project. Specify a new empty output directory:

```sh
python3 run.py --stage lean --project "$PINNED_LEAN_PROJECT" \
  --build "$NEW_EMPTY_BUILD_DIR" --expected-version 4.32.2
python3 run.py --stage kernel --project "$PINNED_LEAN_PROJECT" \
  --build "$NEW_EMPTY_BUILD_DIR"
```

Use the true approved version, not automatically the example. The historical
4.32.0 evidence needs a separate patched-validation pass; see [TOOLCHAIN_NOTICE](docs/TOOLCHAIN_NOTICE.md).
The scripts do not install toolchains, update Mathlib or mutate the old cache.
Lean failures should be repaired without weakening the intended statements.

Rust controls:

```sh
python3 run.py --stage rust
```

A missing compiler is a nonzero NOT RUN result, not a passing stage.

## Important distinctions

**FS coverage is included as work, not claimed completed.** The package provides
adaptive reference-machine probability proofs and code, but literal source
transcript/sampler binding and a uniform adversary-to-ideal coupling still need
real producers. It never assumes all role labels define independent oracles.

**No-grinding honest proving does not mean free adversarial retries.** The exact
security definition and query/time budget must be fixed before a global claim.
The arithmetic diagnostics intentionally flag unsupported lifting of the
reported approximately104-bit conditional residual into global100-bit security.
They are not a forgery or a proof that the target is impossible.

**Prime-field decoders are controls, not the selected QM31/circle extractor.**
The bounded candidate search does not prove candidate availability. Static
mask translation is not full-view adaptive ZK. The small payment-state model is
not the full Token/Registry/forest validator. Cost arithmetic is not a calibrated
all-reachable CU theorem. These limits are stated at the corresponding APIs.

Do not promote conditional consumers as if they constructed their premises.
The master prompt requires independent source producers, exact event coverage,
clean first-party rebuilds and a statement-meaning audit.

## Best order

Reconcile completed repair → run/fix independent primitives → bind actual
transcript and chronological samplers → source/FS coupling → permitted
extractor and payment validator → global probability ledger. Develop adaptive
ZK and all-reachable costs in parallel, preserving their separate claim scopes.

The final release gate is not a count of green Lean files. It is the independent
statement, instantiated source theorem, resource-dependent security ledger,
permitted checked extractor, full privacy proof and exact-profile validation.

## Detailed inventory

See [docs/FILE_MAP.md](docs/FILE_MAP.md) and [results/MODULE_STATUS.json](results/MODULE_STATUS.json) for the scope and status of every Lean draft.
