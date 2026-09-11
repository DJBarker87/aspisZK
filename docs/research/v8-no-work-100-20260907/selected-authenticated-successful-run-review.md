# Same-program authenticated terminal to successful selected run

Status: focused NUC GREEN, v6, seven standard-only transitive axioms audits.
Working parent: `531b50ed6cd06d5902417edf614daee137c19acb`.
Source: `experiments/SelectedAuthenticatedSuccessfulRun.lean`.

## Deterministic endpoint

`phaseProgram` keeps the supplied Program's early C1 prefix/root, OOD data,
ordinary weights and claims, inactive-claim function, and all five causal byte
callbacks. It replaces the previously open C2 total-word field with
`AuthenticatedPhaseWords.fixedC2` at the supplied post-C2 prefix/root.

`fixedInput` is constructed from this SAME program. Its chord is `atGamma`
of that program's data; its word is the raw 26+3 gamma batch; its ordinary
covector and claim are the program's corrected row fields; and its reference
is the actual zero reference. `fixed_before`, `fixed_folded` and
`fixed_phase_word` establish the correspondences rather than assuming them.
No list of 1,048,576 symbols is evaluated in these symbolic equalities.

`source_of_causal` converts the resulting causal relation acceptance into
the existing Program's callback terminal. `successful_of_causal` adds the
independent path checks and constructs `SuccessfulAt`.
`wire_success_or_authentication_failure` composes complete typed q22
multiproof acceptance and the opened-value terminal, yielding:

- the unchanged raw-log collision / C1 late-target / C2 late-target union; or
- `SuccessfulAt` and acceptance of that SAME program's ideal execution.

The already-proved successful-run theorem also supplies canonical parsed
lengths, the accepted-prefix partition and the fixed classifier package;
this adapter consumes it to extract ideal acceptance, without restating or
weakening its full conclusion.

## Premises that remain real obligations

`PathChecks` retains all nonterminal fields of `SuccessfulAt`: canonical
parser success and C1-root agreement for the five actual bodies; checked
OOD inverse; both circle equations and non-west points; nonzero gamma,
kappa, tau and rho. A scalar relation equality cannot establish these facts.
In particular parser failure is totalized in `Bodies.fields`; it must not be
mistaken for canonical parsing merely because the resulting relation holds.

The wire endpoint additionally retains consistent prefix answers, inclusion
of prefixes and every selected hash call in one raw log, actual record
parsing, the complete typed minimal-multiproof run, the actual inverse-lines
result, and the terminal scalar equation on those opened records. It does
not assume opening-to-total-word equality, arbitrary strategy equality,
decoder success, ordinary-row zero, or payment-witness validity.

The remaining source implication is Rust execution to these typed premises,
including the real early-C1/post-C2 cutoffs, the generation of Program data,
weights and component claims, and the transcript's challenge law. Prefix
arguments and bodies have the intended mathematical dependence, but no
Rust/PDA/CPI trace theorem is asserted. Authentication failures are explicit
events, not newly assigned negligible probabilities. Ideal relation
acceptance is not payment extraction.

## Source dependencies

| Source | SHA-256 |
| --- | --- |
| `SelectedWireOpeningTerminal.lean` | `1d5b0f73c728d710fd4529abbd7a7e0edf89e1d061b810703ae464d6614ad7bc` |
| `SuccessfulSelectedVerifierRun.lean` | `b06b23cdf5eb79cd7d8689d50e1f41694a0c487c8d25a67a84b42562da99654f` |
| `FixedWordQueryTerminal.lean` | `6859c7b798e4b05d1103b93bf2604e19562f6b27efbad3fa1e3720833d4b7ff7` |
| `SelectedOrdinaryRowAcceptance.lean` | `ba37ffc3bd10ea8ff9f1d3c082e7059cfc5043a40abbf68cd5275037f16518e5` |
| `AuthenticatedPhaseWords.lean` | `58c8f90bc95b5d5085437b7a554f0da952f4f29bcda22aa8c85162d612f31475` |

No imported source was edited for this adapter.

## Focused proof and evidence

All attempts used the inherited Tailscale NUC runner, Lean 4.32.0,
`-j1 -M9500`, MemoryHigh 8 GiB / MemoryMax 10 GiB / MemorySwapMax 0,
CPU 200%, module maxRecDepth 200 and maxHeartbeats 250000. No larger-cap
retry or local Lean build was used. The runner bootstrap source pin remains
`289d7356c78a4cd493fe61a54f9548f2a0c11298`, not this leaf's working parent.

| Attempt | Exit | Wall seconds | Peak RSS KiB | Swap | Outcome |
| --- | ---: | ---: | ---: | ---: | --- |
| v1 | 1 | 3.18 | 6853992 | 0 | Alias ambiguity and whole-expression conversion |
| v2 | 1 | 2.87 | 6851576 | 0 | Alias fix; remaining whole-word conversion |
| v3 | 1 | 15.62 | 9729732 | 0 | Kernel memory guard in concrete phase-word conversion |
| v4 | 1 | 2.93 | 6853876 | 0 | Dependent-reference rewrite and record projections |
| v5 | 1 | 30.36 | 9729528 | 0 | Kernel memory guard in prefix-containing record projections |
| v6 | 0 | 3.23 | 6891964 | 0 | Generic symbolic projections; all seven audits green |

The decisive correction proves record constructor/update projections with
arbitrary word arguments before substituting the large prefix completions.
This avoids kernel normalization of complete prefix words inside an
`Eq.refl` conversion. A generic folded-oracle projection also aligns its
implicit reference argument before subsequent rewrites. The consumed oracle
function is proved equal; a dependent equality of full oracle structures is
neither assumed nor needed. The private symbolic helpers are included in
the seven public endpoints' transitive axiom checks. Every audit reports
exactly `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or new axiom.

Green tag: `selected-authenticated-successful-run-nuc-v6`. Automatic
pre/postflight both report 1109 exact overlay entries and unchanged
provenance. Native package artifacts remain a pinned-cache boundary, not a
compilation replay. Failed snapshots are retained separately; their manual
postflight PASS results were observed in the tool transcript, while their
runner logs correctly stop at failed Lean exit.

| Artifact | SHA-256 |
| --- | --- |
| Source and v6 source snapshot | `da1643fb2a3140e14a88ed81035fd2029f1d94c2676c35c1c74b4dc0c7ff1479` |
| Green olean | `f2ebf1742d65889862a7a17f9f55073697742c73bef25c844d0025737896debe` |
| v6 log | `a269945a8f95041b71fda3c5a280a98baf7617ec71929bd5e4d7a13ed5950f6b` |
| v6 manifest | `23a383f4f814b2cf8d3bf02568c95afc872ab5797c8c236bf3c104f242c456fb` |

`selected-authenticated-successful-run-evidence.json` records all six exact
source/log/manifest hashes and resource results. The read-only publication
audit requires every retained triplet and JSON fact, but verifies the ignored
local olean only when present; no ignored cache payload is required in a clone.

From the worktree root:

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_selected_authenticated_successful_run.py --check-recorded
git diff --check
```

Publication scope is this Lean source, this review, its evidence JSON and
read-only auditor, plus the six `selected-authenticated-successful-run-nuc-vN`
log/manifest/source-snapshot triplets. The green olean is retained locally
but ignored. No unrelated source, imported green file or cache was edited;
nothing was staged, committed or pushed by this task.
