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

## Authenticated host recovery; remaining source boundary

The archived integration manifest identifies the required transformed
performance image as
`5ded0dbae42449f22e698819d4174f13cf2e9e93f0a195e228011690e008d456`.
The checked-in performance source is the manifest's *before* image. The
retained portable generator does reconstruct an authenticated **initial**
after image, SHA-256
`d5a650022c1cfd76010fd2f307186f800210d306ba0d993233109198245a15e4`,
matching `integration-inputs.json`. Removing exactly the obsolete assertion
`if let Some((statement,_))=&complete_context{assert_eq!(compiled.public_statement,statement.common().lane_transition); }`
that ran **before** statement rebinding yields the selected v4 SHA above,
matching **all four** `evidence/integration-inputs-v{1,2,3,4}.json` manifests.
The later post-rebinding assertion remains. This is a recovered exact source
image, not a proposed production modification. The reusable
`transform_performance_v4` function implements the checked one-line delta.
The relation callback matches both manifests' after image.

This closes and supersedes the earlier report's missing-performance-image
blocker. It does not authenticate the entire generated build or instantiate
the intended fresh-entropy experiment.

The initial transformed image asserts that `ASPIS_V8_MAX_FRONTIER_SCAN` is
absent before the seed loop. It also contains **two** proof-file sinks: a
negative-control write before `continue`, and a positive-path write after
verification. Neither the before-image's optional stress path nor the claim
that every file sink follows successful verification may be attributed to
either transformed image. These are source-text checks, not a build or an
environment audit. The updated audit authenticates the before image, initial
after image, and selected v4 after image separately.

Consequently, neither the ideal uniform-22-subset probability from R14 nor a
source-realizable distinguishing lower bound has been established.  The raw
q4/q6 separator remains a literal encoder result, separate from this audit.

## First remaining proposition

Establish a complete build/call-graph refinement tying the now-authenticated
`5ded…08d456` source, relation callback, transcript implementation,
environmental configuration, failures, and the `proof-{seed}.bin` sink into
one actual q22 publication law.  Only after that may the direct 22/64 sampler
be related to an ideal random-oracle schedule experiment. In particular, the
selected host uses deterministic fixture secrets and an in-memory nonce
store; it is not the intended `generate_for_mask_nonce` adapter.

## Focused literal sampler and exact counting follow-up

See `r15-q22-stopping-evidence.md` for the actual sampler's block-boundary
consumption behavior, last-draw controls, and exact 64-word IID counts. These
narrow the required refinement; they do not remove the source-closure gap.
