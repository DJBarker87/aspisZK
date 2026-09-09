# Censored collector: deterministic growth threshold

`CensoredCollectorGrowth.lean` proves the combinatorial prerequisite for a
censored collector without assuming that retained or accepted queries are
uniform. It contains no probability theorem and imports no Aspis/QM31 tower.

## Exact endpoint

`collectFrom seen trace` recursively unions each retained query set into the
earlier set. `ContainedStep seen trace` records a retained set contained in
the union that existed immediately before it. `contained_iff_prefix` proves
that this recursive event is exactly an occurrence

```
trace = earlier ++ schedule :: later
schedule ⊆ collectFrom seen earlier.
```

`fresh_trace_growth` derives one new index per non-contained retained step
from strict finite-set inclusion; it does not assume numerical growth.
`empty_start_growth` then uses the first schedule's full width: for a
nonempty trace of q-element sets with no contained step,

```
q + trace.length - 1 ≤ (collectFrom ∅ trace).card.
```

`capped_trace_contains` proves the contrapositive for `0 < q ≤ cap`:
if the final union has at most `cap` indices and the retained trace has at
least `cap - q + 2` schedules, a contained step exists. The checked
`q22_cap255_prefix` specializes this to **235** retained q22 schedules and
returns the explicit earlier/schedule/later witness.

The threshold is sharp as a deterministic statement: 234 schedules can
share a fixed 21-element core and each add one distinct new index. Their
union has 255 elements, and no step is contained. This construction is
elementary reasoning, not an additional Lean theorem in this leaf.

## Scope in the recovery argument

The trace can be any adaptively selected retained subsequence. No independence,
uniformity, acceptance-preserving sampling, fixed final polynomial, or
preselected union is needed for this deterministic result. It does not show
that 235 retained schedules are obtained within any attempt budget. It also
does not show that their union is one coherent matching support usable by
the seven-alpha/three-tau/four-kappa recovery theorems. The causal query law,
retention policy, attempt bound and coherent-support linkage remain separate
obligations; a probabilistic charge for the contained event must use its
actual earlier union, not retrospectively freeze the terminal union.

No protocol, proof-body, field, query count, verifier cost or production path
changed. The proof body remains 40,282 bytes. No NUC or external job ran.

## Reproduction and evidence

Research revision: `532ade2064e533602902fc9ae5b4dd90f9207131`.
Concurrent main was read-only at `946ade6f86854c46b24a0291a5ce115749139a16`;
this leaf imports no main Aspis modules. Mathlib source was clean at
`81a5d257c8e410db227a6665ed08f64fea08e997`; direct source/olean hashes,
toolchain and manifest hashes are recorded before and after replay.

From the research root, with a fresh output log path:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_censored_collector_growth.sh docs/research/v8-no-work-100-20260907/experiments/censored-collector-growth-replay.log
```

The runner invokes the cached `lake env lean` environment, Lean 4.32.0,
`-M7000`, a 7-GiB aggregate child-RSS guard and no dependency build.

| Replay | Exit | Lean wall | Peak RSS | Swaps | Result |
|---|---:|---:|---:|---:|---|
| `censored-collector-growth-v1.log` | 1 | 3.90 s | 1,296,498,688 B | 0 | Explicit-prefix witness needed a projected head equality before `subst`; retained failure log |
| `censored-collector-growth-v2.log` | 0 | 0.92 s | 1,309,573,120 B | 0 | All six axiom audits standard-only |

Every retained result audits to `[propext, Classical.choice, Quot.sound]`.
No `sorry` or new axiom is present in the retained source. The v1 diagnostic
includes Lean's temporary failed-declaration `sorryAx`; it is not a claimed
result and does not appear in v2.

Frozen SHA-256 values:

- Source: `fec3a47276af2a40765e3b1976903781d3e0453eee3ff6fb60824bc6ab617ad4`
- Olean: `1858d8160442a144515e6151721b7bd45abcc2d28c8eb314c8790b6b2a95ec42`
- Runner: `1f607cdbe54033cdd87a033acb41276eb56758bcadba373bb8deda373d3f042e`

The next use is a causal censored-collector bound charging a retained
schedule contained in its fixed earlier union. The new theorem supplies
the deterministic reduction, not that probability or a global V8 bound.
