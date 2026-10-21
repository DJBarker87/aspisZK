# Builder continuation 8

Branch `codex/cx-builder-ref8-20261021`, base `71b7f0db3`.

## Stage 1: owned validated-tree carry

Work in progress. The owned reference copies the authenticated empty table
and inner tree and consumes its capability on append. The shipped body is
unchanged. Kani will compare actual append against this reference with
ordered arbitrary parent answers and checked replay inputs.

## Admission, Parts content, runtime and execution

Not yet discharged. No source endpoint premise is claimed removed.

## Frozen program gate

All three optimized SBF rebuilds pass with the final cfg-only registration:

| Program | SHA-256 | wall | peak RSS KiB | swap |
|---|---|---:|---:|---:|
| default | `dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34` | 29.097 s | 446248 | 0 |
| devnet | `fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78` | 3.077 s | 203576 | 0 |
| Pool | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | 32.523 s | 430856 | 0 |

Each has exit 0 and `cmp` exit 0 against the retained frozen artifact.
All actual production inputs in the isolated full build workspace match
this checkout. The inherited cfg-only nullifier reference has older Kani
harness metadata, which does not enter any production build. The narrow
statement extraction workspace also has stale, unused prover siblings and
a narrowed manifest, as inherited from continuation 7; no source identity
claim is made for those unused siblings. Exact pins and receipts are in
`builder-cont8-host-evidence.json`. No binaries are committed.

## Retained unsuccessful experiments

- `tree/kani-full`: compile-time path error; corrected relative path.
- `tree/kani-path`: full-loop symbolic array replay stopped at the
  MemoryHigh review, 195.208 s, 6,393,588 KiB RSS, zero swap. Kani reports
  CBMC status 15, not a solver verdict. No larger-cap retry.
- `tree/kani-fixed01`: fixed trailing-one count with full array replay,
  timeout at 240 s; no owned-tree verdict. Its short selector incidentally
  also selected the inherited glue-tree case 01 (400 checks pass). That
  inherited verdict is not new evidence and does not certify this append.
  GNU time's timeout-parent RSS is incomplete; no true job peak is claimed.
- Initial method and module Charon selectors returned empty/no-function
  extractions. They are rejected even though both tools exited 0. The
  free-function entry selects the actual append loop and result wrapper.
- `tree/aeneas-entry`: nonempty append extraction succeeds (1.979 s,
  132,352 KiB RSS, zero swap), but contains nine unsupported std/opaque
  declarations. It is a diagnostic artifact, not an accepted certificate.
  The isolated owned callback carry extraction is the next narrower target.

## Stage 3 component: primitive path and auxiliary writers

`BuilderPrimitiveWriters` identifies every actual aggregate-extraction
path/aux writer with the previously checked copy writer, including the
complete Result behaviour. The proof uses symbolic suffix induction at
bounds 30, 3, 8 and 24; no trace cell table is reduced. `occRecord` is an
explicit five-field map between the extraction-specific occupancy types.
The twelve theorems cover m31_sub, the complete value writer and both loops,
occupancy row and its loop, auxiliary block, path row base, path level and
its loop, and the complete path block and its loop.

Env J 9324 passes: exit 0, wall 2.59 s, peak RSS 3,746,796 KiB,
zero swaps, all twelve audits use only propext/Classical.choice/Quot.sound.
9321–9323 are rejected elaborations (header parsing, scalar increment lemma
and a local converter name collision), retained with their corrected source
fingerprints. No failed theorem or `sorryAx` result is accepted. This
closes the duplicated primitive path/aux writer identity, **not yet** the
Parts arguments: source tree/chunk/digest/occupancy-inverse correspondence
still has to feed those same checked writers. No Content or endpoint
premise is silently removed.
