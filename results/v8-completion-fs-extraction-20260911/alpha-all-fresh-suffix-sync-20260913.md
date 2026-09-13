# Alpha all-fresh suffix synchronization evidence (2026-09-13)

## Scope

Focused Lean leaf:

`docs/research/v8-completion-fs-extraction-20260911/lean/FSV8AlignedAlphaAllFreshSuffixSync.lean`

Source SHA-256:

`974df435b9754e938372b3a601bf4ecbac454ae0f9ea7b85e4c981f161668efd`

Parent repository revision during the check:

`3e2a3a845e24d3253e4635d4056cdcb6e8e9dbbf`

The leaf proves three deterministic facts.  First, the entire ordered history
suffix appended by all rejected alpha pairs and the accepted pair has the same
input/output/freshness projection as the suffix appended by the aligned
candidate-machine run.  Second, every locally fresh record therefore has an
exact fresh candidate record whose actor is constructed by the actual
`.verifier` machine run.  Third, the complete ordered fresh input/output
enumerations of the two suffixes are equal.

Cached records remain in the projected suffix equality.  The theorem does not
assume that all alpha calls are fresh and adds no target-event or probability
premise.  It still consumes `candidateAligned`; constructing that alignment
from the complete source run is a separate bridge.

## Focused replay

Host: authorised Linux NUC reached over Tailscale at `100.108.41.90`.

Toolchain:

`Lean 4.32.0, x86_64-unknown-linux-gnu, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, Release`

The command used the pinned Lean binary, the recorded V8/V7/mathlib search
path, and a user systemd scope with:

```text
MemoryHigh=7500M
MemoryMax=8G
MemorySwapMax=0
```

The focused command was:

```text
/usr/bin/time -v systemd-run --user --scope --quiet \
  -p MemoryHigh=7500M -p MemoryMax=8G -p MemorySwapMax=0 \
  /home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -o results/v8-completion-fs-extraction-20260911/lean-20260913/FSV8AlignedAlphaAllFreshSuffixSync.olean \
  docs/research/v8-completion-fs-extraction-20260911/lean/FSV8AlignedAlphaAllFreshSuffixSync.lean
```

Result:

```text
exit status: 0
wall time: 3.05 s
maximum RSS: 6,819,232 KiB
swap: 0
```

## Axiom audit

All three promoted declarations report only:

```text
propext
Classical.choice
Quot.sound
```

The checked source contains no `sorry` declaration and introduces no axiom.

## Remaining boundary

This closes the local every-pair suffix/order step.  It does not yet prove
that every cached alpha call is charged to the exact root target event, nor
does it construct `candidateAligned` from the whole accepted verifier run.
Those source/root alternatives remain necessary before applying the routed
alpha probability theorem.
