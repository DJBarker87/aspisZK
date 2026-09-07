# Recovery ZIP review and bounded-family continuation

2026-09-07. Own research base: `cffcc740716f220435bd9a5da05b8fc349c8d3e7`.
Main/source-proof cache inspected at `b2a70154de56c272dafdf67b1293e0523c09cb88`.
Separate V8 branch inspected at `07b66afc22288a6ff460180242b73de4f341e02d`.
No production changes, remote jobs, deployments, or archive uploads.

## Review verdict

The supplied `aspis_v8_recovery_review.zip` reproduces correctly. Its cautions
are important: 7,072,436 is a demonstrated **lower** bound on one recovery event,
not a replacement upper bound. The 2,800-root fixed-family theorem remains true
with its membership hypothesis. No payment forgery has been constructed.

The ZIP has three regular files, 20,352 uncompressed bytes, and no symlinks or
path traversal entries. All files were read before the standard-library Python
script was executed in an isolated temporary directory. Archive SHA256:
`ff038f1ef3341d14b834b9cc933468455766c3ab8753611859cecc3a941c99d7`.
All exact output data matches the packaged results; floating display fields
are excluded from equality decisions. Its 46,875 cases and 10,503 equality
cases pass. An independent falling-product calculation and binary-tree
maximisation recurrence reproduce every q22/q23/quintic row.

Two source qualifications update the review:

1. `Pool/V7FixedWidth29TupleList.lean` already proves a **joint 29-component**
   cap of 100, not merely a per-column list cap. Its restriction to sufficiently
   close tuples, including the old decoder filter, is the issue. It is not an
   adaptive cover of the discarded branches.
2. Newer V8 commits have made the isolated quotient kernels SBF-stack-safe.
   The old 11,904/18,880-byte frames are historical failures. The newer evidence
   still does not establish a complete V8 verifier or full-transaction CU parity.

## Confirmed controls and the actual residual budget

These are **conditional arithmetic screens**, not full security levels. QM31
rows use `L*(b+(1-b)*e_fold) + 396430/(p^4-1)`. The 396430 numerator is eight
K1.5 categories (semantic, copy/lambda, copy/chi, and five small categories),
not just a semantic-sumcheck error. Its applicability to a changed extractor
must still be established.

| Profile | Body model | Over accepted 40282 | Conditional subtotal bits |
|---|---:|---:|---:|
| QM31 q22, 1 target | 40282 | 0 | 104.266742 |
| QM31 q22, 34 targets | 40282 | 0 | 100.019567 |
| QM31 q22, 100 targets | 40282 | 0 | 98.486162 — fails even this screen |
| QM31 q23, 100 targets | 41527 | 1245 | 102.979071 |
| Full quintic q21 | 41692 | 1410 | 100.326664 |
| Full quintic q22 | 42984 | 2702 | 104.402641 |

With no other terms, q22 can afford at most 34 targets and q23 at most 946.
These maxima are not recommended operating points: the q22/34 subtotal leaves
only 1.3471% of the 2^-100 budget. The q23/100 row leaves 87.3173%, an absolute
budget of approximately 2^-100.195660 for **all** omitted accepted-coverage,
authentication, extraction and FS terms together. Privacy remains a separate
requirement, not an invented small additive soundness term.

The quintic q21 and q22 subtotals consume 79.7378% and 4.7280% of the target
budget. Thus the 1,410-byte quintic relaxation buys a thin conditional screen,
not a finished protocol. q22 is the better-margin field-port control, subject
to unchanged field/source/hiding/CU obligations.

q23 does not fit either existing size category: it is 1,527 bytes above 40,000
and 567 above 40 KiB. Its 1,245-byte increment over canonical q22 is exactly
621 query-record bytes plus 624 frontier bytes. Maximum frontier changes
296 to 308 per tree; internal hashes rise 634 to 660 and leaves 44 to 46.
The fixed-field/root/nonce inventory is unchanged in this model. No nonce or
certificate bytes are silently removed, and no new size allowance is assumed.
The domain/dense arrays remain 152 MiB in the model; extra query leakage still
requires a new full-view hiding analysis. This is not measured V8 proving RAM.

## New proved result: the 100-tuple family can cross the counterexample boundary

`experiments/RelaxedTupleFamily.lean` proves the following for the concrete
mathematical log-20 circle encoder:

    For every fixed set of 29 received lanes, all component tuples with
    joint agreement on at least 38,228 symbols belong to a fixed finite
    family containing at most 100 tuples.

The construction ranges over all mathematical tuples and has **no old-decoder
membership filter**. Cardinality follows from the existing joint overlap cap
1024 and the symbolic Johnson second-moment lemma, now at the lower floor.
At the first forbidden size 101 the required strict arithmetic still holds:

    (38228^2 - 1048576*1024)*101 > 1048576*(38228-1024).

This is not merely a cardinality theorem with candidate membership assumed:
the final existential theorem covers **every tuple meeting that closeness
predicate**. It does not assert that every accepted adaptive branch meets it.
The family is mathematical/noncomputable, not a measured efficient extractor.
No new Rust FFT-to-encoder source bridge is claimed.

For the full-fibre boundary construction, the zero tuple has exactly 38,228
joint symbols. It was excluded by the old >=38,230 decoder-backed family but
is included here. Its gamma combination is the selected zero codeword, even at
the exceptional gammas. The old `sharedSupport` field remains false because
the selected combined support has 38,232 symbols. Lowering a filter alone
cannot repair the old `CoherentTraceExtraction` structure.

A second focused lemma proves that C1 subfield recovery can use a tuple's
**own** large joint support. With the existing explicit encoder projection
binding, >=38,228 base-valued joint symbols still force every C1 coefficient
into M31. No old decoder membership or containment of the entire combined
support is needed for this particular descent step. This does not prove
ownership extraction or the earlier semantic/sumcheck links.

An independent exhaustive constant-code analogue over F17 tests the proposed
weakening. It enumerates all 4,913 width-three component tuples and 272
gamma/candidate pairs. The old close family is empty; the relaxed family is
the zero tuple. All 12 high-agreement branches are on that fixed tuple's batch
curve; none has old same-support recovery. This is a permanent small regression
for the distinction, **not** a transfer of toy coverage to the 1024-dimensional
Aspis code. The original full-width Rust counterexample was not rerun unchanged.

## The remaining coverage obligation, with the missing mass visible

Let A denote acceptance, E successful valid-witness extraction, and C the event
that the chosen recovery description is covered. The required partition is

    Pr[A and not E]
      = Pr[A and not E and C] + Pr[A and not E and not C].

The second term must be explicitly bounded. Calling the provider only on C,
returning `none` otherwise, or bounding `Pr[A | C]` does not dispose of it.
Nor should `Pr[not C]` automatically replace it: query rejection can make the
accepted discarded mass much smaller than the discarded-prefix mass.

There is also an **inequality-direction trap**. Johnson bounds a family whose
members have joint agreement **at least** a floor. The fixed-target query lemma
uses an **upper** bound J on the target's matching fibres. The <=100 close
family cannot simply be substituted into `100*choose(9557,q)/choose(T,q)`:
some close targets have many more matching fibres. A valid proof must classify
close false targets through the semantic/relation events and separately control
uncovered/far/adaptive candidates. The ZIP labels its covering hypothesis
unproved; its arithmetic does not commit this error.

The concrete next theorem should weaken the old same-support extractor to:

- a fixed pre-challenge family with joint closeness and correct C1 descent;
- representation of the recovered combined/final objects by a member's batch
  and fold, or an explicit accepted-residual failure event;
- early semantic and adaptive-C2 causality, component-OOD/scalar consistency,
  and an explicit bound on accepted branches not represented this way.

The new relaxed family handles the known threshold counterexample's membership
boundary. **The general adaptive batch/fold representation bound is still open.**
It cannot be supplied by assuming `Width29CandidateOnCurve`, `candidateMember`,
or the old correlated-agreement loss at a new name. A complete q23 cover must
also respect the pre-gamma/pre-alpha target and independent-query hypotheses
of the fixed-target lemma; the existing ROM resources are not grandfathered.

## Current engineering evidence, reused rather than rerun

At `07b66afc`, `results/v8-a100-q22/sbf-stack-and-cu-20260907.md` records:

| Isolated probe | Reachable kernel frame | Probe transaction CU |
|---|---:|---:|
| Heap-batched quotient | 2176 B | 807012 |
| Pointwise quotient | 2112 B | 791539 |
| Canonicality parsing alone | 192 B | 634879 |

These use a 39,934-byte syntactically canonical **packed-fixed** zero fixture,
not our 40,282-byte canonical-fixed model and not an honest accepting proof.
The quotient modes defer canonicality. They omit authentication, folds,
terminal checks, settlement and CPI. Do not add these independent totals or
compare them as complete V8 transactions. A combined parse/kernel attempt
exhausted 1.4M CU; that rejects that straightforward probe shape only.

One uncalled convenience helper still has a 4736-byte frame. The working probe
separates its parser and prefix stages. No new full-transaction parity result
exists, and the unexpectedly cheaper 88-inversion path on this special fixture
does not establish a general inversion-cost advantage.

## Decision after this continuation

Keep canonical QM31 q22 as the in-budget research direction. Retain q23 as a
**labelled size-relaxation control**, not an approved new protocol. Use quintic
q22 as the better-margin conservative field-port control, with q21 retained
as its thinner, smaller comparison. None meets every requirement today.

The next deciding experiment is the adaptive batch/fold representation theorem
for the relaxed family, charging accepted discarded branches. Stop any proposed
proof at an assumed membership/representation hypothesis or an uncharged event.
Do not start a wholesale implementation merely because the conditional table
passes. See [cover-results.json](cover-results.json) and
[coverage-evidence.json](coverage-evidence.json) for exact data and execution scope.

Reproduce the independent review and controls from the research worktree root:

```sh
python3 -B docs/research/v8-no-work-100-20260907/experiments/recovery_cover.py --review-dir /path/to/extracted/aspis_v8_recovery_review
```

Omit `--review-dir` to run our parameter/coverage/toy harness without the ZIP.
From the cached `/Users/dominic/ZK/AspisFormal` workspace:

```sh
/usr/bin/time -l lake env lean /Users/dominic/ZK/.worktrees/ZK-v8-no-work-100-20260907/docs/research/v8-no-work-100-20260907/experiments/RelaxedTupleFamily.lean
```
