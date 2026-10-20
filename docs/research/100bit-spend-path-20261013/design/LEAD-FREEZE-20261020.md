# Lead decision: the frozen R1 verifier (2026-10-20)

Codex job cx-pin (3ab179fc9) ran the combined gate set on research b2727acd3
(adopted compact binary-multiproof format + stage-2 refactor + deployment-id
data slots): default/devnet `.text` byte-identical with the id slots at
offsets 1,470,512 and 1,470,544; stage-2 cone extracts with the pinned
Charon/Aeneas (LLBC identical after normalising the destination filename and
short-name ordering); all standing gates pass (P_R1 8/8, retry loop, D78
simulations, mutations, double spend, strict stack audit); six-fixture CU
within PREREG-PROOF-SIZE-2 item 1 with minimum margins 281 CU (stage 1) and
134 CU (settlement); Pool rebuilt to 121f3e29….

**Decision.** The verifier source at research b2727acd3 (verifier-crate file
hashes, toolchains and ELF pins in
`evidence/freeze-20261020/FREEZE.md`; default verifier ELF dfc2a91a… (1,507,400 bytes), devnet-id build fb2fc048… (same size), stage-2 LLBC f11e40b4…)
is the frozen R1 verifier for the soundness theorem (gap-map step 0,
superseding LEAD-REVIEW-FORMAT-ADOPT-20261020.md and the two amendments).
Every re-pin (S1–S10), the stage-2 refinement (R14), the tx1_finish
extraction (R15), the query bound (R19) and the final CU bound are stated
against this revision. Any later verifier source change reopens all of
them and needs a new freeze decision.

Launched on this freeze: cx-tx1-finish (R15), cx-cu-bound4 (final CU bound,
same method as cu-bound3), cx-devnet3 (deployment with the devnet-id build).

Note: the pin evidence was committed at the repository root (`evidence/freeze-20261020/`); it is to be relocated under `docs/research/100bit-spend-path-20261013/evidence/` once the jobs that cite the root path have landed.

## Next-freeze candidate (2026-10-20, parked)

Branch `codex/cx-freeze-prep-20261020` (commits f6639066e, 0e340502c,
92e30def9; retained unmerged; it subsumes codex/cx-tx1-finish-prep-20261020,
now deleted) carries the checkpoint-serialisation refactor that lets the
tx1 finish cone extract, and the generated-import hygiene fix (stage-1 and
stage-2 generated modules import together). All standing gates pass on it:
P_R1 8/8, prover/simulator 33/33, D78 simulations, 13 runtime scenarios,
six-fixture CU with minimum margins 119 CU (stage 1) / 134 CU
(settlement); default/devnet `.text` identical. Candidate pins: default
verifier 4aa7e8a1…, devnet b5a81324…, Pool 121f3e29… (unchanged).
Adoption rule: taken as the next freeze once the S1–S10 re-pins against the
current freeze have landed; at adoption the lead re-runs the all-input CU
bound, re-checks the re-pins whose cones the refactor touches (S8:
tx1_finish) and the R19 constants (checklist in
`evidence/freeze-prep-20261020/FREEZE-CANDIDATE.md`).

## Candidate update (2026-10-20, prep2)

Branch codex/cx-freeze-prep-20261020 now also carries the accumulation-path
split (ba6ed8989: optional batch dispatch outside the loops, separate
batched/unbatched helpers, copy-valued reads) that lets the candidate-7
cone translate; re-gated (6306b3959): all gates pass, margins 119/134 CU,
candidate pins default 73cf9fd5…, devnet ea9cb9cd…, `.text` identical.
Pending on the candidate before adoption (prep3, one pass): the
`compact::check_values` `chunks_exact` loop (S8), the `Iterator.any`
interface gap (R13), and the two generated-name collisions
(stage-1/stage-2; `Stage2ContinuationTypes` vs
`AspisR1PublicPreparation.Types`), with every admitted-route cone extracted
on the result.

## Sweep v1 (2026-10-20): stopped on CU; candidate kept at prep2

The one-pass sweep's indexed refactors of compact/semantic/weight code
(trial commit fc62e4705, moved to branch codex/cx-sweep-trial-v1-20261020)
regress stage 1 on transfer-255 to 1,204,246 CU, 4,679 over its B1 figure
(the adoption criterion of PREREG-PROOF-SIZE-2 item 1), and Aeneas still
fails in the inactive-weight reduction. The parked candidate branch is
reset to the gated prep2 state (6306b3959; pins 73cf9fd5/ea9cb9cd). The
next sweep keeps a per-change CU ledger and admits only changes that keep
stage 1 ≤ B1 on every fixture.

## Candidate update (2026-10-20, prep4 — ledgered sweep)

Branch codex/cx-freeze-prep-20261020 at 9d726fc3f (source ed0027cfb): 22
ledgered iterations (132 fixture measurements); the retained borrow
restructurings SAVE 224 CU on stage 1 and 1,774–1,779 CU on settlement per
fixture; minimum margins against B1 now 343 CU (stage 1) / 1,910 CU
(settlement); all gates pass (P_R1 8/8, simulator 33/33, D78, stack audits,
`.text` identity); joint generated-type imports pass. Newly translating:
the values/inactive cone (LLBC fb4f18d5…) and the Libra cone (b5aa456f…).
Candidate pins: default 98067cc7…, devnet 016bb79c…, Pool 121f3e29….
Remaining blockers: the mask expansion, `echeck`, the semantic boundary,
`wide_view`, and the missing `Iterator.any.default` interface; the only
translating split form found for expansion costs +796 CU (453 over
transfer-255's B1).
Ruling for prep5: (1) std-library iterator interfaces that the pinned
Aeneas lacks (`Iterator.any.default` and any like it) may be supplied as a
small, reviewed Aeneas library model in the extraction harness — listed
explicitly under premise P6 with a differential test against Rust `std`
behaviour on the admitted inputs; (2) the borrow blockers continue under
the same CU ledger, with more forms; any blocker still needing a CU
increase is reported with its cheapest form for a user decision.

## Candidate update (2026-10-20, prep5) and the ruling on the last two cones

Branch codex/cx-freeze-prep-20261020 at 2318acd43 (production source
c16e59e77): `wide_view`, the semantic boundary and `echeck` resolved within
the CU ledger; two P6 iterator models (`Iterator.any.default` and the slice
`any`) bound with explicit instance arguments, 21,208 differential cases
against Rust std passing; 12 cones re-extracted with has_errors=false, 10
translating in Aeneas (scanner, boundary, view, borrow owners, Libra,
values/inactive, scoped stage 2/finish/candidate 7); all gates pass;
margins 748 CU (stage 1) / 1,910 CU (settlement); pins default f9ecbc27…,
devnet 3f21a42f…, Pool 121f3e29….

Two cones remain: the compact-field expansion (cheapest translating form
+4,431 stage-1 CU per fixture, 3,683 over transfer-255's B1 and most of the
5.4k worst-case margin — not taken) and `Weights::new`'s unsafe
initialisation (no translating form). **Ruling:** both are proved by a
Rust-level equivalence route instead of rewriting the shipped code: a
translatable reference form of each function is written beside the shipped
one (test/extraction-only, never compiled into the program), Kani proves
the shipped and reference forms equal for all inputs of the fixed admitted
sizes (the repository already uses Kani for V5: `kani-verif/` on main), and
Aeneas extracts the reference form for the Lean proofs. Kani's soundness on
these harnesses joins premise P6 by name. The shipped bytes and CU are
unchanged.

## Candidate update (2026-10-21, prep6 — Kani)

Branch codex/cx-freeze-prep-20261020 at 0e29da6a2: the compact-field
expansion cone is CLOSED by the equivalence route — six Kani harnesses
(Kani 0.67.0, bundled Kissat 4.0.1; main's V5 bundles pinned 4.0.4, the
difference recorded) prove shipped ≡ reference for symbolic inputs with
unwinding assertions, and the reference extracts with has_errors=false;
default/devnet ELFs unchanged (f9ecbc27…/3f21a42f…). Still open on
`Weights::new`: the constructor equivalence (bound 11 stopped at the
ten-minute review under memory pressure, 6.4 GiB; not retried), the
constructor reference's extraction (InterpBorrows 2731) and the broader
caller (`prepared_claim`, Not_found), and allocation-failure equivalence
(Kani's default allocator does not fail). Ruling for prep7: decompose the
constructor proof (per-loop harnesses with Kani loop contracts or function
contracts so no single harness unrolls the whole constructor), reshape the
reference until it extracts, and treat allocation failure as abort-
equivalent: on Solana a failed allocation aborts the transaction in both
forms — stated as a named runtime fact under P2 with a host test of the
abort path, not proved in Kani.

## Candidate CU bound (2026-10-21, cu-bound5)

The all-input bound on the candidate (pins f9ecbc27…/3f21a42f…/121f3e29…,
reproduced exactly), same pre-registered method as cu-bound4: PASS over the
admitted split [3,10] — B_stage1 1,293,948 (transfer) / 1,293,330
(withdrawal), B_settlement 1,267,581 / 1,280,616; minimum margin 6,052 CU,
better than the frozen build's 5,440 (the ledgered restructurings saved
CU). 746 accepted runs, 17,206 branches classified, zero unexplained
variation or violations (`evidence/cu-bound5-20261020/REPORT.md`). The
adoption checklist's CU item is therefore satisfied for the candidate as it
stands; a further source change (prep7's reference forms are cfg-gated and
leave the ELFs unchanged) would need a re-check only if the ELF moves.

## Candidate update (2026-10-21, prep7 — Weights::new)

Branch codex/cx-freeze-prep-20261020 at d8578002f: the functional
constructor reference now extracts (has_errors=false); nine supporting Kani
harnesses pass (row-level pieces); allocation failure is tested through the
shipped constructor and error mapper for all three variants (rollback stays
the named P2 runtime fact); ELFs unchanged (f9ecbc27…/3f21a42f…). Open: the
row equivalence and assembly/ownership composition of the constructor proof
(resource-heavy attempts stopped, caps not raised), and the broader caller
`prepared_claim`, which hits a pinned-Aeneas internal error
(`Not_found`, InterpReduceCollapse.ml:1991) reached through `Weights::pair`.
Ruling for prep8: (1) finish the constructor equivalence by composing the
nine passing harnesses with Kani function contracts (`stub_verified`) so the
assembly harness only reasons about the row-level contracts; (2) for
`prepared_claim`, reduce the Aeneas internal error to the smallest
reproducing Rust function, then either reshape a cfg-gated reference form
around it (Kani-equivalent, as for the expansion) or record the minimal
reproducer as a tool defect with the exact construct, for a decision on a
tool upgrade.

## Candidate update prep8 (lead, 2026-10-20 night)

Parked branch `codex/cx-freeze-prep-20261020` at 3aa3caf0e (not merged; the
candidate is adopted only after session A's re-pins). Route translation stays
10/12. `Weights::new`: supplied-row ownership and assembly proved via
verified store contracts (87 s, 2.25 GiB, zero swap); full row arithmetic
still unproved, stopped without raising caps. `prepared_claim`: the pinned
Aeneas failure is reduced to a one-iteration `Box<u8>` read loop; the scalar
helper translates and its Kani composition passes, while three full callers
still fail. Candidate ELFs unchanged (`f9ecbc27…`, `3f21a42f…`). prep9 is
running: verified primitive field contracts plus per-row `stub_verified`
harnesses for `Weights::new`, and per-caller harnesses for `prepared_claim`,
with no change to candidate source.

## Candidate update prep9 — track parked (lead, 2026-10-21 00:40)

Parked branch `codex/cx-freeze-prep-20261020` at ce345a4bd (not merged).
prep9 proved the M31/CM31 modular contracts and QM31 add/sub against
independent specs, bound the exact-source Lean QM31 multiplication proof,
and passed the direct product cell. Still 10/12 cones: the full
statement/circle rows of `Weights::new`, constructor composition, and all
three `prepared_claim` caller comparisons. No unverified stubs and no
larger-cap retries. Candidate ELFs unchanged (`f9ecbc27…`, `3f21a42f…`,
1,529,128 bytes). Lead decision: park the candidate track. The release
proofs target the frozen verifier (`dfc2a91a…`), adoption waits for session
A's re-pins, and prep9 cost about 0.9M tokens for one cell. Resume with the
two open cones when the user wants the 1.19M CU candidate adopted.
