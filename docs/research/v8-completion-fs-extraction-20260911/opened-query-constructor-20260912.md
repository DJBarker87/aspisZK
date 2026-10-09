# Same-body opened-query constructor and literal positive scalar update

Base: `d0e56c281ea545832cfaec97334139fcbff8a440`.
Branch: `research/v8-completion-fs-extraction-20260911`.
This is a deterministic connection milestone, not global soundness completion.

## What is now constructed

`SameBodyOpenedRun.run` is a total Option-valued functional pipeline. It runs
the existing fixed-wire parser, canonical packed-record parser, checked ordered
inverse constructor and both-tree multiproof verifier on the SAME derived
wire, records, query positions and chord data. `run_checks` derives their four
success equations. `merkleRun` constructs the historical `SuccessfulMerkleRun`
from this result; it is no longer an independent input to the new endpoint.

`run_authenticated_opened_or_failure` consequently derives the 22 opened
quotient/fold values from that pipeline, or the existing concrete shared
digest-collision / C1-late-target / C2-late-target alternative. There is no
independently supplied decoded record, inverse array, total received word,
opened-value array or successful Merkle certificate.

`SameBodyQueryClaimExact` interprets the existing `SameBodyQueryClaim`
`powersFrom`, `scales`, zipped `foldl`, `increment` and **positive**
`injectClaim` in a commutative ring. Induction derives their finite sums;
the increment is not redefined to equal the desired mathematical answer.
The prior scalar is unrestricted. Subtraction belongs in the discrepancy,
not the source scalar update. The quarter parameter is irrelevant to this
query calculation; the exact-field consumer uses the literal `1/4`.

`SameBodyOpenedQueryUpdate.successful_opened_query_update_or_failure` then
consumes the functional pipeline result. Its final polynomial is read from
the SAME parsed wire at indices 441..696. `finalFromWire_canonical` derives
canonical decoding from those exact body fields. Its conclusion is:

```
sourcePositiveUpdate - sum_i rho^(i+1) * finalEvaluation_i
  = prior - rho * sum_i actualPrefixQuotientResidual_i * rho^i
```

or the unchanged authentication failure. The left-hand update uses the actual
source-shaped list accumulator, and its openings are the constructed pipeline
values. No separate final or openings are supplied. No polynomiality,
image-validity, provider-success or successful-witness premise was added.

**This is not yet the entire carried-functional discrepancy.** The displayed
subtracted sum is the *injected query contribution*. Producing the original
functional, its updated covector and the correct prior discrepancy remains
necessary. Likewise this pipeline is a pure functional decomposition: its
order is not a claim about effectful Rust calls or their chronological log.
In particular, this pure pipeline computes inverses before authentication;
the inspected Rust path authenticates first. A chronological source lifting
must preserve Rust's order, especially the calls retained on rejection.

## Authentication prefix producer now uses the real old types

`FSV7PrefixBridge` imports the actual historical `RawHashInput`, `Digest208`
and `AnswerPrefix`, not lookalike definitions. It proves UInt8/Fin256 byte
round trips, exact 26-byte digest projection and the source leaf/node input
grammar. `chronological_old_prefixes` converts the extended causal FS run into
both historical answer-consistency premises, both inclusion premises and
literal chronological prefix-take identities. These are conclusions rather
than caller-supplied agreements.

The complete hash answer remains 256 bits in the interpreter; truncation is
only the 208-bit authentication projection. No independence or probability
law is inferred from the conversion. The view's unqueried-input default is
not evidence of an actual oracle answer.

Still required to join this producer to the opening endpoint:

* Same body roots as the actual C1/C2 root outputs at their respective cuts.
* A concrete later script emitting all leaf and internal-node calls, proving
  the existing `callsIncluded` premise rather than supplying it.
* Actual source/adversary-to-script coupling across continuations.

A relevant source detail: the pure `runPass` definition recursively computes
its tail before forming the current parent, while its recorded trace prepends
the current C1/C2 calls. An effectful lifting must execute those current calls
first, then prove equality of pure results and the exact chronological trace.
Blindly inserting hash effects into the pure recursion would get this wrong.

## Premise and remaining-obligation ledger

| Boundary | Status in the new opened-query endpoint |
|---|---|
| Wire/record parser, inverse and functional Merkle successes | Derived from one `run = some result` |
| Openings and final256 | Constructed from that run/body; not separate inputs |
| Source-shaped positive query scalar | Exact ring proof from the existing accumulator |
| Same query ordinal through records/inverses/fold | Preserved |
| OOD/chord `Data`, query schedule, alpha/rho | Inputs; actual parsed-field/transcript producers still open |
| Prior scalar and original/updated carried functional | Full source connection still open |
| Authentication answers/prefix inclusion | New actual-type FS producer exists; full root/call-history composition open |
| Complete semantic terminal, later relation responses and `SuccessfulAt` | Not constructed by this partial pipeline |
| Literal Rust execution refinement | NOT RUN / remains open |
| New full payment nonvacuity or mutation fixture | NOT RUN in this continuation |
| Permitted-access checked witness extraction | Still open; no algebraic-existence substitution |
| Global probability composition / FS resources | No new numerical bound; unsupported terms remain uncharged |

The functional success premise is execution of the independently defined
four-check pipeline, not an alias for ideal acceptance. It must not be renamed
complete selected-verifier success. Full-view adaptive ZK and all-reachable
complete-transaction CU remain separate obligations.

## Executed checks

Historical Lean 4.32.0 (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`), via Tailscale
on the NUC, one scoped job at a time; MemoryHigh=8G, MemoryMax=10G,
MemorySwapMax=0, RuntimeMaxSec=600. Every accepted receipt has exit 0 and
pre/postflight input hash validation. The old overlay stays unchanged.

| Target / evidence directory | Wall seconds | Peak RSS KiB | Swaps |
|---|---:|---:|---:|
| `SameBodyOpenedRun` / `opened-v3` | 2.917 | 6,683,860 | 0 |
| `SameBodyQueryClaimExact` / `query-exact-v2` | 1.115 | 1,811,248 | 0 |
| `SameBodyOpenedQueryUpdate` / `opened-update-v4` | 3.318 | 6,686,584 | 0 |
| `FSV7PrefixBridge` / `fs-old-7-v3` | 3.018 | 6,539,024 | 0 |

All promoted endpoint axiom output contains only standard foundations.
Evidence lives under `results/v8-completion-fs-extraction-20260911/`; receipts
record exact compiler commands, search paths, source/import/artifact hashes
and output hashes. No `.olean` files are committed. These are historical
cached-import leaf checks, **not** a fresh rebuilt Mathlib/old Aspis closure,
patched historical-chain certification or independent kernel validation.

The two source-shaped scalar modules and seven FS modules were compiled from
their recorded sources in the historical environment before their consumers.
Two FS proofs required cross-version compatibility: a symbolic list-index
lemma replaces the unavailable historical `List.getElem_idxOf`. Statements
are unchanged. The changed seven-module FS closure independently rebuilt
successfully under 4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), pinned
Std reused, in `FSAuthenticationSuffix-q_b2ygjv`. Fresh replay for these changed
sources is NOT RUN; older fresh-replay receipts certify their older snapshots.

Reproduce that focused source closure from this directory:

```sh
python3 FocusedLeaves.py --root FSAuthenticationSuffix
```

For historical consumers, use `HistoricalLeaf.py` with the exact overlay,
package, manifest and supplement documented in the prior connection reports,
a fresh output directory, and each recursively required `--prior-leaf`
receipt directory. Recorded commands are executable examples for the existing
authorised runner. Recreating that pinned source/cache environment elsewhere
remains a prerequisite, not an implicit network fetch or source rebuild claim.

### Preserved failures and repairs

* Opened constructor v1: concrete parser case splitting caused recursion
  failures; a generic Option-bind success lemma replaced it. v2 exposed a
  missing namespace and unnecessary reduction of concrete parsing; explicit
  scope and local opacity fixed v3. No resource cap raised.
* Query arithmetic v1: unfolding the arithmetic record expanded an unrelated
  evaluator before the induction hypothesis matched. v2 keeps that record
  symbolic and proves only the required recurrence/list identities.
* Opened update v1-v3: metavariable-driven equality composition attempted
  costly concrete-field definitional reduction. v4 states the intermediate
  sum equality explicitly and rewrites the named source identity directly.
* Historical FS exposure v1: missing library lemma, not a false theorem.
  Original source snapshots and failed receipt retained; the replacement is
  symbolic and works in both checked versions.
* Prefix bridge v1-v2: byte round-trip/library elaboration and expansion of
  fixed-length arrays; explicit constructor identities and narrow list-map
  rewrites repaired these without altering the grammar or theorem.

Failed logs may print `sorryAx` for Lean's error placeholders; they are marked
FAIL and excluded from retained checked endpoints. No `sorry` or new axiom was
introduced into the successful source chain.
The frozen source headers retain their pre-check draft wording so the checked
source hashes remain exact; the receipts and this report state the subsequent
historical-check status, not a patched or global certification.

A separate read-only agent reviewed the constructed inputs and endpoint
statements before this closeout. It confirmed the same-body opening/final
producers and identified the prior/covector, root-match and chronological-call
boundaries above. This is an agent review, not an external kernel or human
cryptographic audit.

## Decision and next experiment

The independently supplied opening array has been removed from this query
update path, and the final now comes from its same body. The next decisive
source step is a chronological script for the selected two-tree opening loop,
with exact roots and emitted-input trace, then composing the constructed
prefix premises with this opened pipeline. In parallel the carried-functional
producer still needs to consume this positive update and the same later
responses. Neither step is a new local-bit estimate.

No protocol, proof-format, production acceptance or deployment change.
Maximum body remains 40,282 bytes; grinding security credit remains zero.
Global security claim supported by this continuation: **none**.
