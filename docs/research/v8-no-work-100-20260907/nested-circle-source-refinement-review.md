# Nested-circle source refinement: exact first-hit locality

`experiments/NestedCircleSourceRefinement.lean` is the first focused
predecessor for whole-run controller refinement. NUC v2 is green: six checked
declarations and six standard-only axiom audits. No whole controller, sampler-mass, fresh-oracle,
or Fiat–Shamir result is claimed by this leaf.

## Exact source interface

The ordinary prefix decoder supplies its own consumed block count. The
new endpoint `ordinary_first_hit_cut` proves that count is positive and at
most four, the input is exactly its consumed prefix followed by the returned
suffix, the consumed prefix reproduces all output fields with empty
remainder, and every strictly shorter block prefix fails. No expected trace,
honestly generated tape, decoder-success wrapper, or supplied cut equation
is substituted for these conclusions: the sole success premise is the
literal ordinary source call under examination.

This preserves the source's rounded block discard: unused words in the
last consumed block stay inside that consumed block; later whole blocks are
unread. The unread-prefix replacement theorem changes only the returned
suffix and preserves every other output field. Its V7 predecessor's
redundant `targetLong` premise is not needed by the proof.

`ordinary_strict_prefix_none` uses append stability and the actual returned
count bound. It does **not** conflate `none` with exhausted retries: detailed
short-input versus hard-failure classification remains in
`NestedCircleRouting` and needs additional preservation lemmas before the
whole controller can be composed.

## V7 reuse and cache boundary

Borrowed pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

- `V7Tag73VariablePrefixGammaSampler.lean`, lines 106–263: the three
  proofs `decodeLimbs_take_wordsUsed`, `flattenedWords_take_blocks`, and
  `decodeOrdinaryPrefix_take_blocksUsed` are narrowly ported unchanged.
  Source SHA: `5395e710e188f1f7e2085fbf84304fd040215446be7349d75061a540e22dea1f`.
- `V7Tag73VariablePrefixGammaFlatRouting.lean`, lines 658–679: unread-prefix
  replacement proof, with the redundant length premise removed.
  Source SHA: `f99a9cd8160535f3bab41c6bb87bc775ff7d39cabe431b00aed1a0981f214041`.

Both borrowed files were checked unchanged against that pin. The entire
GammaSampler/FlatRouting/SemanticTranscriptBridge import closures are not
imported: their extra cached module variants do not match the current
overlay. Direct imports are only frozen `NestedCircleRouting` and pinned
`V7Tag73SamplerDecoderExact`, whose source/olean hashes are respectively
`b4bfdf70bf94fec863454edf05e0d31342c0a83db2a123f9ecd5aaa961ee1db8` and
`1134465da320635cb21479c3e0dd3daae7cff534b8b143bcd03daba06eeed41c`.
No dependency export or cold build is needed.

## Remaining whole-run bridge

A source continuation interpreter can represent each reachable controller
state, including its pending prefix and the exact unread suffix. The next
step is one-block preservation: an accepted `pending ++ [answer]` must have
empty whole-block remainder, a hard failure must persist under append, and
four blocks cannot still require input. Induction over actual block reads
then connects the first circle3 call and distinct3(circle3) on its returned
suffix to the controller. No fixed disjoint four-block windows are allowed.
The final nested record's `blocksUsed` describes only the last ordinary
call, so total consumption must accumulate the proved cuts.

Even that deterministic run theorem would not itself prove a finite-tape
mass identity or freshness law. Named destination uniqueness and actual
source lookup, followed by the appropriate pre-answer/stopped-prefix law,
remain separate interfaces.

## Focused build evidence

Working source parent: `d0e3196848b89de8ddf1a85fcc0a6e55bf8fdc95`.
Inherited runner scope parent: `289d7356c78a4cd493fe61a54f9548f2a0c11298`.
Both attempts used Tailscale numeric IP `100.108.41.90`, the existing pinned
cache and inherited 8 GiB high / 10 GiB max / zero-swap scope. The exact
Lean 4.32.0 command is retained in each log (`-j1 -M9500`, target
`NestedCircleSourceRefinement`, runner `run_higher_y_nuc.sh`). Preflight
showed no other user build scope and 43 GiB available. No dependency was
rebuilt. Native package artifacts remain a pinned-revision cache boundary,
not a package replay.

| Attempt | Exit | Wall seconds | Peak RSS KiB | Swaps | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| v1 | 1 | 3.41 | 6648828 | 0 | The four reused/locality declarations checked; strict-prefix proof failed only at record-projection elaboration. |
| v2 | 0 | 3.26 | 6682216 | 0 | Explicit intermediate and `appendOrdinaryRemaining` simplification fixed that projection; six standard-only audits. |

Every attempt's `.log`, `-source.txt`, and `-manifest.json` is retained under
`experiments/nested-circle-source-refinement-nuc-vN`. The failed version's
temporary `sorryAx` entries are not release evidence; v2 contains none.
Final source matches its exact snapshot byte-for-byte. The successful
postflight checks all 875 entries and records `PROVENANCE_UNCHANGED=true`.
Both sessions were terminal before the sole compiler slot was released.

Final SHA-256:

- Source/snapshot: `8e4afcb38782a6eeb2736c66e74e533c81bfcc0c59b7d48854101198d70c2945`.
- Olean: `1836391d1daff359c10cf6814133a97ca57ac91dfebd2d2b83441783cb044550`.
- Log: `87513b652552dc83a06a56db576399f7b2c2cffd42eeeefd5461ab4641438629`.
- Manifest: `091a1595c5845e4cac20b59104526cee0d596e809b4c8ca791a5328d4d15c533`.
- Runner: `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

No old proof, production source, protocol default, or cache boundary was
edited. No second proof leaf, full regression, arithmetic gate, or FS/mass
experiment was run.
