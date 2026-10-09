# Fixed second-phase C2 word and opening alternative

Status: **kernel-green on the first focused NUC attempt**. Both declarations
use only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or new
axiom. No existing Lean file was edited and no dependency was rebuilt.

[AuthenticatedPhaseWords.lean](experiments/AuthenticatedPhaseWords.lean)
retains the exact checked bytes, including its original source-review header.
The status above supersedes that header without an unnecessary source edit
and replay. Its SHA256 is
`58c8f90bc95b5d5085437b7a554f0da952f4f29bcda22aa8c85162d612f31475`.

## Deterministic result

`fixedC2 records root` is literally
`c2Received (AuthenticatedEarlyC1Prefix.prefixWords records root)`. It uses
the second-phase answer prefix, after lambda/chi and before OOD/gamma in the
intended source execution. It does not replace the earlier C1 prefix.
`fixedC2_eq_actual_view` proves equality to the same partial-path word under
any oracle extending the recorded answers. Thus no unknown future answer is
an input to this construction.

`accepted_c2_opening_prefix_or_late_target_or_collision` consumes one
same-root accepted C2 sibling path, consistent recorded answers, inclusion of
the prefix in the full oracle log, and coverage of that supplied path's hash
calls. It proves exactly one of these alternatives (not claimed disjoint):

- The prefix-completed C2 word contains the exact disclosed packed leaf and
  shared salt at the opening position.
- `C2OpeningLateTargetHit`: a later supplied-path input hashes to the first
  unresolved C2 target selected by the prefix resolver.
- The existing shared `RawLogTruncatedDigestCollision` occurs.

The opening position may be adaptive. No q16 wrapper, invented hash error
term, or global canonicality premise appears. Missing/noncanonical values
are still totalized only in the field-word definition; the good branch fixes
raw bytes and salt before the packed canonical parser is invoked.

## Reuse and remaining source interface

The only direct import is `AuthenticatedEarlyC1Prefix`. The proof mirrors its
green C1 argument using the pinned V7 C2 interfaces:
`resolvedC2Path_yields_covered_prefix_opening`,
`c2_covered_opening_is_projection_or_raw_collision`,
`resolveC2Path_none_iff_firstUnresolvedC2Target_isSome`, and the generic
`authenticatingPath_of_bottomUpOpening`,
`firstUnresolvedTarget_yields_later_hit_or_collision`, and prefix-view
congruence theorem. No new generic Merkle machinery is needed.

The next deterministic consumer can build `PairedOpening` directly from
`PackedQueryRecord.c1Bytes/c2Bytes/saltBytes`, combine the early-C1 and later-C2
alternatives, and use `c1_entry/c2_entry` plus
`V7ExtractedLaneWords.c1_received_of_exact_projection` /
`c2_received_of_exact_projection`. This supplies the exact local `matchAt`
required by `SelectedPackedQueryBridge.matching_fold`, without replacing the
fixed words by its post-query `observedWord`.

Actual minimal-multiproof success must still construct the sibling paths and
their covered hash traces, with the original record/query order. A caller
cannot substitute an arbitrary `Program.c2` for this constructed C2 word;
that field/root/prefix binding remains a required program-construction
change. The two cutoffs and full shared-oracle log must come from the actual
execution. Authentication rejection, parser rejection and missing source
coverage are not assigned negligible probability here. No transcript sampler,
Fiat–Shamir, witness extraction, or payment-validation theorem is asserted.

## Focused execution and evidence

Working revision: `531b50ed6cd06d5902417edf614daee137c19acb`; the unchanged
draft originated at `eb06c838bdeb002508dac2b4af406631f3d67e66`. The inherited
runner retains bootstrap revision `289d7356c78a4cd493fe61a54f9548f2a0c11298`
and borrowed V7 pin `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

```text
bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  AuthenticatedPhaseWords authenticated-phase-words-nuc-v1
```

Tailscale preflight found no live Lean/lake compiler and approximately46.6GiB
available. Lean4.32.0 ran with `-j1 -M9500`, depth200 and heartbeat200000,
inside its own `MemoryHigh=8GiB`, `MemoryMax=10GiB`, `MemorySwapMax=0`,
`CPUQuota=200%` scope. Exit0; wall2.78s; peak6,702,780KiB RSS; swaps0.
The1089-entry pre/post import checks passed unchanged. Native package
artifacts remain a pinned-revision cache boundary, not a replay claim.

The exact imported authentication artifacts were previously registered
copy-only; the incompatible native `V7MerkleFirstUnresolvedBinding` source
variant was not substituted. This focused consumer now checks that retained
import combination. It does not retroactively claim a dependency rebuild.

| Artifact | SHA256 |
| --- | --- |
| [Frozen source](experiments/authenticated-phase-words-nuc-v1-source.txt) | `58c8f90bc95b5d5085437b7a554f0da952f4f29bcda22aa8c85162d612f31475` |
| [Log and both axiom audits](experiments/authenticated-phase-words-nuc-v1.log) | `4453564c29b188d162b87271b5a5ad54d5566e493e842578e981d374721a1cc7` |
| [Per-run manifest](experiments/authenticated-phase-words-nuc-v1-manifest.json) | `ee06b65f00890515404d10b21e043e62218b2b56a787bd2d6beb6962ec39e463` |
| Local ignored `.olean` | `477a6bab127526d2ea9f7ecffdf62ab951c315813b61ba12e6f7f59ed06bb7a3` |

[Machine-readable evidence](authenticated-phase-words-evidence.json) records
the exact results. All artifacts were copied and hash-checked locally. The
ignored `.olean` is optional for publication; the source/log/manifest/JSON
remain unconditional evidence. No nested-circle or stopped-prefix artifact
was changed, staged, or used as a new dependency. No commit or push was made.
