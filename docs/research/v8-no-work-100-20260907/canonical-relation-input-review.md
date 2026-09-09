# Canonical fixed bytes to compact relation responses

Research base: `503332fbe747db381fc8ee67c4bbdd3631ec97cf`, branch
`research/v8-no-work-100-20260907`. The worktree was clean at inspection.
Only new proof/runner/evidence files are owned by this task; concurrent work
and all existing checked leaves/runtime code are preserved.

## Exact source projection

The active structured callback calls the same `relation_callback.rs::parse`.
Its fixed section is **697 canonical 16-byte QM31 values**. The parser first
checks the complete body length, then decodes every fixed field. The new
projection models that control flow as a short-circuit list collection of the
retained exact little-endian codec, rather than assuming a byte/value
correspondence predicate.

The source guard is exactly:

```text
length < 24890
 OR length > 40282
 OR (length - 11228 - 22*621) mod 52 != 0.
```

Consequently an admitted length has the form `24890+52*f`, `f<=296`.
The source splits the remaining bytes equally between two 26-byte-node
frontiers. This shape result does not prove either frontier authenticates.

Each fixed field reads bytes `16*field+byte`, with `field<697` and
`byte<16`. A successful projection proves those reads are within the
input, so the totalized mathematical `getD` fallback is not used.
The actual Rust nested field decoder therefore receives full 16-byte chunks,
not arbitrary short slices. Rust machine/slice safety is still not translated
by this field/list model.

## Response grammar and V7 reuse

| Wire fields | Meaning |
|---|---|
| 359..387 | First 29 component OOD answers |
| 388..416 | Second 29 component OOD answers |
| 417 + 6*round + sent | Four rounds, six values per round |
| 441..696 | Final256 coefficients |

The six received values become the existing `RelationRoundParts` fields
`c0,c1,c2,c3,c5,c6`. The compact polynomial keeps all six in positions
`[0,1,2,3,5,6]` and reconstructs only `c4=claim*quarter-c0`.
The existing boundary theorem applies when `quarter*4=1`. This task does
not re-prove the relation repair probability or assume that a sent polynomial
is correct.

The exact M31/QM31 codec and generic compact grammar are reused from the
formalization consumed by V7. V7's 641-field wire offsets are deliberately
**not** reused: the V8 two-component-vector OOD layout moves the relation and
final offsets to 417 and 441. The older V7 fixed-field source bridge still
requires a `FixedFieldDecodeExact`/source projection premise; this new
modeled parser derives its own coordinatewise decode property from success.

## Fail-closed scope

The kernel-checked statements establish:

- Every bad body length returns no fixed-field vector.
- Every noncanonical limb, anywhere among all 697 fixed fields, rejects the
  complete fixed-section projection.
- Success gives exactly 697 values, with each value decoded from its own
  input bytes and all fixed-byte reads in range.
- Each round's six typed response values and all final256 values are those
  exact decoded fields.

The model intentionally collapses the source `Length` and `Canonical`
error variants into `none`. It does not purport to check query-record
canonicality or Merkle roots/frontiers in this early parser stage, nor does
it make the later response transcript globally non-adaptive. All bytes in a
concrete input body are fixed; the separate causal game quantifies the prover
responses at their actual challenge boundaries.

Still unproved here are the compiled UInt8/u32/Vec execution, literal chunk
iterator/slice translation, account/public context parser, hash transcript,
authentication and source-to-entire-game/replay coupling. No correctness
predicate for those missing layers is assigned a small probability.

## Checked interface and evidence

| Result | Hypothesis and conclusion | Scope |
|---|---|---|
| `CanonicalCollect.success_ofFn` | Short-circuit collection succeeds: exactly the symbolic number of values, each decoded from its corresponding input | Generic list proof; no 697-element normalization |
| `length_shape`, `malformed_length` | Exact source length guard; admitted lengths are `24890+52*f`, `f<=296`; bad lengths reject | Body shape, not frontier correctness |
| `parse_success`, `success_in_bounds`, `fieldBytes_exact` | Actual modeled collection succeeds: all 697 coordinate decodes and exact in-range byte reads | No assumed decode/source-projection predicate |
| `noncanonical_field`, `noncanonical_reject` | Any limb at least `2^31-1` rejects, including fixed fields outside the selected round | Exact retained little-endian codec |
| `decoded_response`, `decoded_final` | The typed relation/final values are the decoded bytes at the literal V8 offsets | Four rounds, six scalars each; 256 final coefficients |
| `compact_keeps_six`, `compact_quartic`, `decoded_boundary` | No sent coefficient omitted; only c4 reconstructed; compact boundary equals incoming claim | Reuses the existing quarter-inverse/compact grammar |

Source pins (all unchanged from the research base):

- `experiments/relation_callback.rs`: SHA-256 `285c90695cc7558a88ffc7cb50de4235b68c7ceed9d0600d5cc9ba7f682607ed`, parser lines 86–91 and compact construction line 82.
- `experiments/structured_weights.rs`: SHA-256 `06befd20c084234ce1afa2d7cf3612a12370fdb0e98e95db30d89cf245b51089`, active response/final reads at lines 178, 181 and 194.
- `crates/aspis-core/src/field.rs`: SHA-256 `5795495e2fa9ad85e097c2ad96ffc826aaad3c16afc0e0bd00459f9f51068cd8`, nested canonical field decoder.

The runner verifies imported research source against `503332fb...` and
borrowed formal source against `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
It checks recursive source/olean hashes before and after each focused target;
the new generic dependency also has its own source/olean pin file. Concurrent
cache HEAD `c7347eefcf767c375040f8f73160995a7886e3ae` does not substitute for
those per-source checks. No source or olean in the borrowed worktree was changed.

Both successful logs record `PROVENANCE_UNCHANGED=true`. Commands, source and
olean hashes, toolchain, failed checks and exact measurements are in
[the evidence JSON](canonical-relation-input-evidence.json).

`CanonicalCollect.lean` is kernel-checked: its short-circuit collection
returns a coordinatewise decode relation and the exact symbolic list length.
The successful focused v2 run took 2.38 seconds, with 1,265,254,400 bytes peak
RSS, zero swaps and exit 0. Both axiom audits contain only standard Lean
axioms. The v1 failure was a missing `List.GetD` import, not a resource failure;
the import was added without increasing any limit.

The dependent `CanonicalRelationInput.lean` is also kernel-checked. Its v2
run took 11.40 seconds, with 5,608,521,728 bytes peak RSS, zero swaps and exit 0.
All eleven audits contain only `propext`, `Classical.choice` and `Quot.sound`.
The retained v1 failure records a lexical spacing error (`<m31Modulus` was
parsed as another notation); the replacement added whitespace, without
changing the theorem or resource cap. The failed v1 logs are diagnostics,
not claimed theorem evidence.

Reproduction from this worktree, using fresh log names:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_canonical_relation_input.sh CanonicalCollect /tmp/aspis-canonical-collect-replay.log
bash docs/research/v8-no-work-100-20260907/experiments/run_canonical_relation_input.sh CanonicalRelationInput /tmp/aspis-canonical-input-replay.log
```

These are two serialized cached leaves, not a full formal replay. The runner
resolves the cached Lake environment and invokes its Lean executable with
`-M7000`, independently guarding aggregate child RSS at 7 GiB. No unchanged
dependency was rebuilt. macOS has no systemd cgroup; zero observed swaps are
recorded, not claimed as an OS-enforced swap prohibition.

## Unchanged budget and next boundary

No source operations, proof values, masks, transcript messages or protocol
parameters change. The maximum body remains 40,282 bytes. No SBF or full-
transaction CU, proving-time or global security result is claimed. The
remaining objective is acceptance-to-checked-payment extraction under the
declared raw/Fiat–Shamir resource regimes, not just successful parsing.

The next useful parser boundary is the later 621-byte packed query record:
derive its C1/C2 slot projections, gamma recombination and canonical rejection
in the actual four-slot order, then connect those decoded values to
`SelectedQueryBuffer`. This task has not silently treated fixed-field parsing
as that query-record or whole-verifier refinement.
