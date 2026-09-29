# R67: exact circle-map extraction obstruction

Base revision: `8de551b22484de15f0407f80d9257154043d3b04`.
Date: 2026-09-29. Diagnostic/source-tool milestone, **not a new proved bridge**.

## Result

Attempting the complete selected `secure_ood_circle_point_from_parameter`
closure exposed a precise toolchain coverage gap. The unchanged source extracts
to LLBC successfully, but Aeneas rejects a first-class pure conversion function
item inside the guarded QM31 multiplication helper. An extraction-only
eta-expansion gets translation past that point, but the resulting output has
**seven external axiom declarations** for unmodeled standard-library operations.
That output is diagnostic evidence only and is **not imported or accepted as a
proof**. No new Lean target was compiled and no new theorem is claimed.

The R66 inverse proof remains valid. This is neither a discovered protocol
failure nor evidence that the full circle map has been proved.

## Executed experiments

Both used the selected R62 source stage, pinned Charon/Aeneas binaries,
`nightly-2026-06-01`, release/offline/locked extraction, and explicit overflow
checks. The five inputs are `field.rs`, `circle.rs`, `r23_width.rs`,
`r24_guarded_qm.rs`, and `r25_checked_dot.rs`. All 197 stage pins were checked.
No repository or selected-runtime source was edited.

| Experiment | Target | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| Original unchanged source | Charon extraction | 0 | 1.08 | 223084 | 0 |
| Original unchanged source | Aeneas translation | 2 | 0.39 | 79552 | 0 |
| Eta-expanded diagnostic copy | Charon extraction | 0 | 1.11 | 223404 | 0 |
| Eta-expanded diagnostic copy | Aeneas translation | 0 | 0.60 | 90344 | 0 |

Jobs ran sequentially in requested systemd scopes with MemoryHigh=5 GiB,
MemoryMax=7 GiB, MemorySwapMax=0 and TasksMax=128. Both terminated; there is no
live build to resume and no memory-pressure failure to retry with a larger cap.

Original stage: `/home/dombarker/project-offloads/aspis-r67-extracted-20260929-a`.
Diagnostic stage: `/home/dombarker/project-offloads/aspis-r67-extracted-20260929-b`.

## Original failure

Aeneas reports `Unimplemented` at `SymbolicToPureTypes.ml:444`, attributed to
`r24_guarded_qm.rs:4–25`. The retained translator source shows the rejected
condition: a first-class function item's forward signature is required to have
`effect_info.can_fail`. The helper passes the pure `u64::from` function to two
array maps. This is a translation limitation, not a failed integer bound.

The controlled diagnostic changes exactly two occurrences:

```rust
.map(u64::from)
// becomes, in the disposable extraction copy only:
.map(|value| u64::from(value))
```

Both source versions and the exact diff rule are pinned. Four other source
files remain byte-identical. The callback does not capture state, but **no
formal original-Rust-to-normalized-Rust theorem or new Rust differential test
is claimed**. This normalization is not silently accepted into the proof trust
base; its acceptance remains an explicit obligation if that route is used.

## Missing library coverage

The eta output contains 43 local functions and six opaque external functions,
plus one external type. Aeneas also warns that the runtime iterator trait lacks
`chain` and `any` fields. The seven generated template axioms are:

- `core.iter.adapters.chain.Chain` (type);
- `core.array.Array.map`;
- `core.iter.traits.iterator.Iterator.chain.default`;
- `core.iter.traits.iterator.Iterator.any.default`;
- `core.iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator.next`;
- `core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any`;
- `core.option.Option.ok_or`.

The templates are retained **under evidence only**. Renaming them, importing
them or filling them with unproved assumptions would not close the source
obligation. Translation exit zero does not mean the output compiles or proves
the caller correct.

The exact matching Rust standard-library source files are retained for the
next step: array map, iterator methods, chain adapter, slice iterator macros
and `Option`. The existing Aeneas iterator model and the two relevant translator
source files are also pinned. For example, the actual `Option::ok_or` body is
a `Some`/`None` match, but that simplicity does not justify accepting its
generated axiom without a concrete model/source correspondence.

## Next source obligation and route

Provide source-grounded, axiom-free support for the used array/iterator/option
operations, and address pure-function-item lowering (or verify and explicitly
accept the eta normalization). Preserve callback evaluation order, callback
state, short-circuiting, iterator state and failure propagation; do not replace
generic `FnMut` callbacks with a pure-map assumption. The particular canonicality
predicate and widening conversions are pure, but the library model must state
its exact supported scope rather than assume that for every callback.

Then prove the current guarded QM31 product and complete circle-map execution,
retaining singularity-before-subfield error order, and connect the bounded
sampler to its observer model. The existing raw-product arithmetic and R66's
inverse closure should be reused, not re-proved as substitutes for these
missing source links.

This is an actionable source-tool obstruction, not a declaration that the
overall goal is blocked or complete. Full shared-oracle/seed/commitment laws,
all transcript observations, visible failures/retries/publication and justified
privacy loss bounds remain open. Pre-beta quotient-pair extraction remains a
separate soundness obligation.

## Evidence audit

`evidence/r67-circle-source/` retains both LLBCs, commands/environments, logs,
both source versions, raw diagnostic outputs, rejected templates, source files
for the missing standard-library operations, and a manifest/receipt. The checker
distinguishes successful **evidence auditing** from the still-open source bridge:

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r67_obstruction.py
```

Result: evidence audit PASS, source bridge OPEN, seven external axioms rejected,
zero new Lean theorems. No runtime/SBF changes or reruns; retained primary CU is
**1,497,377 / 1,498,764**, and both actual 1M runs still exhaust.
