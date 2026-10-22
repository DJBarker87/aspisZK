# S4 next-freeze recommendation

Recommendation: adopt the existing proof-friendly combined candidate as the
next research source freeze, permitting its measured CU regression against
B1 while retaining the 1,400,000 CU transaction budget. This is not a
deployment request, security claim, or waiver of proof/re-pin obligations.
Production research source has not been changed by this recommendation.

## Concrete source and artifact

The three candidate blobs are taken from
`e47c7390c31883b4b4a4289ba23ada3396fd107c` on
`codex/s4-combined-candidate-20261021`. That historical branch also contains
other experimental source changes in its ancestry and must not be merged
wholesale. The retained gates below exercised baseline
`b2727acd3abf79315d18b754a260f58f4b1c6326` plus only these three blobs.
A clean current-research review overlay is commit
`5b23a95e6386a02fe12540403aa46067ee167c0d` on
`codex/s4-three-source-review-20261022`, based on `369647a72`; its current-base
checks are separate from those historical receipts. The candidate files are:

| File | Candidate SHA256 | Purpose |
| --- | --- | --- |
| `fast_dots.rs` | `53fa714e84ded64b844061f4d1b66ad20ee1ba48c3873a73970f80ede8a0b602` | Explicit four-call entry, eight-coordinate updates and reductions, ordered tail pushes |
| `fast_pairing.rs` | `2cb96261cecfd766b5e1b45a585b74c5f59c20c6be4f41e806239e2786ca7313` | Four explicit checked-Q comparisons |
| `weights.rs` | `28b558ffa9f5b004188c7f50b1597fe681186f54fb4d52a3bd125df4f2481137` | Existing indexed early-powers candidate |

All paths are under `crates/aspis-r1-cost-probe/src/`. Candidate verifier ELF
SHA256: `40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0`.
The artifact remains a candidate; it is not the deployed/final pinned target.
The compact 57,607-byte proof format, binary18 Merkle multiproofs, admitted
split10, two-transaction structure and cryptographic parameters are unchanged.

## Proof progress supporting this choice

The literal source-body-checked V10 candidate entry is total on the specified
scanner/canonical-coefficient inputs and returns the four canonical values
with literal field-result equations. No arbitrary arithmetic backend or
independently successful old implementation is supplied. See
`evidence/s4-concrete-v10-candidate-endpoint-v1-20261021/`.

The actual candidate helper/outer are independent of both arrayFromFn and
wideLimbCount. More strongly, the candidate entry and callback are unchanged
when those two operation slots would diverge if invoked, and totality/field
results still hold. See `evidence/s4-v10-no-fromfn-kernel-root-v1-20261021/`.
P6 is a mathematical reference inside the proof, not an unsupported operation
whose Rust correspondence must be assumed for candidate execution. The
frozen original's Std/from_fn gap remains unresolved.

The exact candidate checked-Q push has a full-Result correspondence to the
concrete QRaw backend in
`evidence/s4-checked-q-push-bridge-v1-20261021/`. The concrete record projection
uses that existing result; the raw input field-coordinate parser lemma is
supplementary. Registered Aeneas models and extraction/compiler trust remain
explicit.

One source-installed candidate tx1 success yields all ten actual query calls,
and each actual returned dots array is tied to four canonical field results
for a shared ClaimPowers vector. See
`evidence/s4-candidate-tx1-output-fields-root-v1-20261021/`. The settlement
source-installed resume/prefix analogue covers twelve actual calls, deriving
its starting cursor from the split guard; full tx2 caller reachability is
still open. See
`evidence/s4-tx2-resume-twelve-field-evidence-v2-20261021/`. Upstream concrete
scanner/preparation and checkpoint/driver bindings remain required for the
global theorem; they are not discharged by the local S4 arithmetic result.

## Measurements and the policy change

Thirty standing commands passed on the combined candidate. The completed
NUC receipts, six fixture reports and artifact/text identity are now retained
in `evidence/s4-combined-standing-retained-v2-20261021/`; its checker verifies
those existing results without rerunning the suite. Six functional
fixtures, strict stack checks and fourteen mutations passed. Highest measured
stage1 CU is1,210,100; highest settlement CU is1,189,265. These are fixture
measurements, not analytical all-input bounds. All are below the configured
1,400,000 CU limit. The candidate fails the existing B1 CU comparison on all
six fixtures; those failures must remain recorded.

A separate retained current-format OS-random/full-mask proof was accepted by
both artifacts: stage1 1,196,068 frozen /1,206,885 candidate; settlement
1,139,924 frozen /1,150,423 candidate. One sample does not establish mask-value
cost independence. See `evidence/s4-full-osmask-current-cu-control-v1-20261021/`.

The current `design/LEAD-FREEZE-20261020.md` says the sweep admits only changes
keeping stage1 at most B1 on every fixture. Adopting this candidate requires
an explicit exception to that performance criterion. It does not change the
100-bit per-attempt criterion, transparency, setup assumptions, or transaction
count. No exception has been recorded by this report.

## Work required after a source adoption

Retain separate old/candidate source pins and the historical failed gates.
Regenerate the complete admitted-cone inventory against the adopted three
files; reconcile S1/S3/S4/S5/S9 and caller/S8 declarations whose body hashes
change, rather than attributing old proof pins to the new source. Reconcile
the weights candidate's own source/equivalence/totality obligations. Rebuild
and pin the final deployment artifacts and call-count inventory after all
adopted source changes, rerunning affected gates only. Compose S4 with the
actual upstream S1/S2, checkpoint and complete caller contracts, replace the
S10 placeholders with implementation instances, and perform the final coherent
proof-closure replay with standard axioms and complete release receipts.
All other global soundness/source/runtime/Fiat-Shamir obligations persist.
The implementation-linked100-bit target is not yet established.
