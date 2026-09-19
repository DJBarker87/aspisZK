# R15 archived q22 source-slice audit

Date: 2026-09-19.  Branch: `research/v8-privacy-repair-20260913`.

## Result

The checked-in archived relation callback contains a direct q22 sampler:

1. absorb `V6_FINAL256`;
2. absorb the final eight bytes of the supplied grinding nonce;
3. call `challenge_queries_without_replacement(22, 2^18, 64)`;
4. absorb `AV8/query-batch/v1`; then sample `rho`.

In the visible default branch of the paired archived performance slice,
`ASPIS_V8_MAX_FRONTIER_SCAN` being absent causes one direct invocation of
that callback.  There is no q22 candidate-selector or frontier cap in that
default branch.  The optional environment-controlled stress branch instead
searches nonce suffixes until it finds a schedule with frontier 296, so it
cannot be included silently in any uniform-schedule or publication law.

This is a literal, static source-slice result only.  It does not prove that
the transcript oracle outputs are IID, identify the deployed environment, or
bind the slice to a complete generated build and its sole publication path.

## Reproducible audit

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/audit_r15_q22_source_slice.py
```

Exit status: 0.  The audit pins the relation callback SHA-256 to
`285c90695cc7558a88ffc7cb50de4235b68c7ceed9d0600d5cc9ba7f682607ed`
and checks the stated ordering and parameters.  It also pins the checked-in
performance slice to
`989a55cf3779ea4f4df54fd75cac8265b8ca820464e4e064f141742ef50a9661`.

## Source-closure failure

The archived integration manifest identifies the required transformed
performance image as
`5ded0dbae42449f22e698819d4174f13cf2e9e93f0a195e228011690e008d456`.
That image is not present: the checked-in performance source is the
manifest's *before* image.  In contrast, the relation callback does match its
listed *after* image.  Thus those two slices cannot be treated as one
authenticated transformed source closure.

Consequently, neither the ideal uniform-22-subset probability from R14 nor a
source-realizable distinguishing lower bound has been established.  The raw
q4/q6 separator remains a literal encoder result, separate from this audit.

## First remaining proposition

Supply and authenticate the transformed performance source
`5ded…08d456`, then establish a complete build/call-graph refinement tying
that source, the authenticated relation callback, transcript implementation,
environmental configuration, failures, and the `proof-{seed}.bin` sink into
one actual q22 publication law.  Only after that may the direct 22/64 sampler
be related to an ideal random-oracle schedule experiment.
