# Sampler diagnostic — 2026-10-27

No premise removed. S2/A2 and the 100-bit target remain open.

## Q1 Native
Frozen source revision `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`, scratch-only cfg(test) wrapper, `cargo test --release --locked --offline -j4`. SDX_R003 passed.

| Block | Digits | Quotient |
|---|---|---|
| P | [0,1,0,0,0,0,0,0] | 0 |
| zero | [0,0,0,0,0,0,0,0] | 0 |
| P+1 | [1,1,0,0,0,0,0,0] | 0 |
| 32 ff | [255,2048,7168,14336,17920,14336,7168,2048] | 256 |

Graph validated against frozen Cargo.lock before each test launch; offline and lock hash unchanged (SDX_graph.json, SDX_lock.json). R001 failed before compilation because c3 path source was not yet copied; R002 failed on scratch println without std qualification; R003 corrects that wrapper. No timeout or memory kill.

## Q2 Emitted
The phrase “the SAME function of the adopted release extraction” has a provenance obstruction. The manifest `docs/research/100bit-spend-path-20261013/design/D188-PROVENANCE-FINDING-20261027.md` and the trust appendix select **AspisR1PublicPreparation.Funs**, an adapted historical cohort, at:

`docs/research/100bit-spend-path-20261013/lean-candidates/s1-prepared-claim-carrier-bridge-20261020/sources/AspisR1PublicPreparation/Funs.lean`

SHA256 `544b75b962ade326ff1069b6986805a175cc90db1c592b1c524dffcd94693d2d`. It imports Aeneas and Types, **no FunsExternal**, and contains **no low_base_p_digits definition**. Therefore four concrete Results for that nonexistent declaration cannot honestly be supplied. This is a precise obstruction to Q2's requested attribution, not a substituted proof.

The actual indexed sampler dependency in the coherent/adopted proof cohort is `AspisR1Post25Sampler.Funs`, from:

`docs/research/100bit-spend-path-20261013/lean-candidates/post25-ordinary-sample-candidate-20261020/sanitized-sources/Funs.lean`

source SHA256 `f02a8fc4503304c2630052a116be257ef507780ffe166844e1b08d71e0e9ec11`; object SHA256 `4fc184f23d7427726cf8dee25e77792736ae508a252c799523d73bbbaee894ad`, matching SInt2's selected object manifest. It imports Aeneas and Types, **no FunsExternal**. Its own extraction manifest calls its source a candidate-only indexed sampler; its loop explicitly stores each quotient. `SDX_cohort_pin.json` records that association without promoting the candidate source to frozen Rust.

`SDX_Cohort.resultP/resultZero/resultP1/resultFF` (L032) prove its complete Results equal the Q1 table, using inherited success/refinement theorems, a 32-byte positional-rank closed form and eight small Nat divisions. These are cohort-model results, not a new source-refinement proof.

The raw twelve-leaf release-kit Funs is instead:

`evidence/extraction-assoc2-20261027/XRj_L013/sources/XRj_generated/XRh_Release/Funs.lean`

SHA256 `f4b2d17c061ce7062d64146531788b6448328e656fb6dbd6192f2d61db31a3b5`. XRh_PINNED-RESULT expressly says emission alone establishes neither elaboration nor adoption. The retained XRj_L013 log reports incompatible mutable Iterator/FnMut and from_fn Result signatures (especially lines 3693, 3705, 3766). There is no admitted unadapted executable environment in which to assert four raw Results. No raw file was repaired or compiled with an axiom template in this job.

For the **XRn kit**, `SDX_kit_manifest.json` pins all 17 original files and the solely name/import replacement `XRn_Join → SDX_Join`. Inverting that replacement reproduces the originals exactly. All were rebuilt privately against SInt2. `SDX_PResult.emitted`, `SDX_ZeroResult.emitted`, `SDX_P1Result.emitted`, `SDX_FFResult.emitted` prove:

| Block | XRn complete Result | Receipt |
|---|---|---|
| P | ok([0,0,0,0,0,0,0,0],2147483647) | L023 |
| zero | ok([0,0,0,0,0,0,0,0],0) | L025 |
| P+1 | ok([1,1,1,1,1,1,1,1],2147483648) | L027 |
| 32 ff | ok([255,255,255,255,255,255,255,255],4294967295) | L029 |

Each uses eight separately proved emitted loop steps, a finite loop composition, eight separately proved byte-word reads and a symbolic constant-callback traversal. No whole sampler recurrence was normalized. L033 audits the eight complete Result theorems and the P disagreement. All accepted prints contain only propext, Classical.choice, Quot.sound (or a subset).

## Q3 Location
**The first loss is in the pinned Aeneas-emitted Funs body, not in a project from_fn external.** Exact declaration:

`sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body`

Raw file above, declaration line **3599**, loss at **3624**, SHA256 `f4b2d17c061ce7062d64146531788b6448328e656fb6dbd6192f2d61db31a3b5`. It binds `let (o, iter1, next_back, _)`, discarding the fourth mutable restoration callback, then `let _ ← dividend / i3`, and invokes only `next_back r`. No quotient value or cast is passed to any writeback. In frozen Rust sampler.rs:63 the same quotient is cast and assigned to `*limb`.

XRn's corresponding declaration is line **3598**, loss at **3623**, in `evidence/extraction-assoc6-20261027/XRn_Join_Funs.lean`, SHA256 `16c90d850002f705d0f48799368d60f08c4dab9994dfeb891c9f25162d99612b`. `SDX_loss_location.json` verifies **byte equality of these entire loop bodies after replacing only the reverse-next callee name**. Thus this loss precedes XRn's worker adaptation. The body is supplied by the pinned translator (XRh records binary `c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958`, extended source tree `3be6820e84debbb8f2cc6b61abca478e98157bc7`), not a pinned std-library definition. As a release-source translated body it is a D188 translation-fidelity finding under the owner's body-scoped ruling; it is not repaired by an external-adapter equivalence claim. This does not establish that this new raw file is imported by the adopted root.

Additional, distinct definitions explain the kit's actual unchanged rank:

| Definition | Provider and trust position | Exact location / SHA256 |
|---|---|---|
| XRn_Join_reverseNext | Worker-only ABI adapter; third return restores original item; fourth permits updated item. Separate adapter row, not newly accepted D188/std trust. | XRn_Join_ABI.lean:14; `3847689d5653b9bdddf3c5367410fb6e71b38b661a5c7075a06607f7dfae9020` |
| mutable IterMut.next_back | Project external supplied for worker kit; append-back reconstruction. Separate model/adapter obligation. | XRn_Join_StdExtra.lean:48; `b0701bcefaa8453f30354f61343944eab9e4187d5f483fc0798a8fc12ec88e57` |
| XRn_Join_revRestored | Worker adapter applies the restoration function to the captured **initial** iterator. On these runs this appends eight old limbs to the original eight (length 16). Separate adapter row. | XRn_Join_ABI.lean:37; same ABI hash |
| Array.from_slice | Pinned Aeneas std model: returns original array if restored slice length differs. It is the fallback being reached, not a silent quotient assignment. Library base is in P7; validity of this caller's restoration remains an obligation. | retained source `evidence/pv-srcid3-20261026/sources/research-Aeneas.Std.Array.ArraySlice.lean:23`; `8baf9750f4ac40780e6ab0b7d4da7cb010d05a52aaff5cab8636551562a799c1` |
| core.array.from_fn | Project kit external returns only values and discards final closure. Used only for the immutable byte decoding in this sampler. | XRn_Join_FunsExternal.lean:87; `34439b3f94e5fd8c3e529e5f64fd7feba2683174363d354fef93ac79f6b1b179` |
| XRn_Join_fromFnState | Worker adapter explicitly retains final capture; **this** is used for the mutable digit callback. Separate adapter row. | XRn_Join_ABI.lean:29; same ABI hash |
| SelectedMaskProbe core.array.from_fn | Project-supplied external, not Aeneas's generated definition: final capture discarded at line 108. No evidence that it is the external for this sampler. | `docs/research/100bit-spend-path-20261013/lean/TerminalArrayFromFnModelV4.lean:102`; `a28d4d0bcf907ec59adf6204bcbdc9606da1b7068a67edb18b926130ebe0227f` |

The generated from_fn template is an axiom interface, not an implementation or an approved extra axiom. The trust appendix expressly excludes arbitrary extern templates. A state-dropping function of type `F → Result (Array T N)` cannot simply be substituted for the raw sampler's second call, which destructures an array **and** capture. The retained raw elaboration failure confirms this seam. No external here is repaired or newly trusted.

## Q4 Scope
The scan is of the full raw twelve-leaf emitted Funs (hash above), not just sampler.rs. `SDX_calls.json` records patterns, complete matching declaration text and line numbers. All direct mutable-array iterator consumers besides the finding are:

| Shipped source function | Emitted locations | Mutated state / exposure |
|---|---|---|
| multiproof::verify_in_place | loop0_loop0.body:1277, iter_mut:1353; nested loop0_loop0_loop0.body:1154 and enumerate-next:1174 | Enumerates mutable children, writes selected child bytes and restores the child array. Same iter_mut / mutable back-functions / Array.to_slice_mut restoration family; no mutable reverse call. |
| verifier::update_residue_row | function:1994, mutable into_iter:2009; loop1.body:1960, next:1968 | Flush rewrites four residue limbs. Same IterMut.next and mutable-array restoration family; not from_fn or mutable rev. |
| sampler::add_small_base_p | function:3519, mutable into_iter:3524; loop.body:3475, next:3484 | Rewrites base-P digits and carry. Same IterMut.next and mutable-array restoration family. |
| verifier::BatchedWeights::finish | function:6398, iter_mut:6402; finish_loop.body:6348, enumerate-next:6365 | Writes calculated QM31 weights into the borrowed weights slice and restores it. Same iter_mut/enumerate/back-function family. |

There is **no other mutable IterMut.rev caller** in this Funs. The other from_fn callers are `verifier.candidate.query_values` (:2865), `r1_semantic.verify_finish` (:5732 and :5736), and `verifier.QueryGeometry.for_range.closure_4...call_mut` (:6559). Their callbacks only read captures; no captured write requiring returned state is present. The first byte-decoding from_fn in low_base_p_digits is likewise read-only. Thus low_base_p_digits is the sole captured-mutation from_fn site in this emitted file.

For completeness, the generic Rev family also occurs at `r1_semantic.semantic_value` (:5465 rev / :5469 fold): shared polynomial reads with an explicit fold accumulator, no borrowed capture mutation; and `verifier.QueryGeometry.for_range_loop0_loop0.body` (:7332 next, constructed at :7405): reverse range traversal with explicit suffix-inverse/Vec state and Vec.index_mut writeback, **not the mutable-slice Rev instantiation**. These are not evidence of the same defect. The tables are an exposure inventory, not findings that the other functions are incorrect. Opaque leaves have no emitted bodies to grep; no completeness claim covers those native internals.


## Classification and consequence

**(c) Pinned raw release-kit emission already discards the quotient write; XRn adapter restoration additionally retains the old rank; the adopted historical cohort is a distinct indexed model, so this is a translation-fidelity/adapter-association finding, not an established adopted-external-only defect.**

For D188: the owner's trace reading does not cure a missing mutable write in a specifically translated source body. This raw body's attribution must be reported as a finding before it can receive D188 release credit; neither the generator's success nor a hand-supplied external authorizes assuming it faithful. Existing theorems about the selected cohort remain theorems about that cohort. These four matching cohort fixtures do not prove general frozen-source fidelity, nor does this packet identify an already adopted root's from_fn external as the culprit. The trusted translation boundary and the untrusted worker adapter obligations must remain separate. No whole-root invalidity or deployed Rust/ELF bug is asserted.

For **A2**: its first all-blocks sampler equality is false for this selected kit (fresh L033 plus reused XRp counterexample). A2 and dependent ordinary/gamma/scratch association remain OPEN. No premise removed, added, weakened or reclassified; no new trust, metric, game or release-source adoption. Report the raw emission finding to the lead; repair/re-extraction belongs to the adopted extraction owners, not this diagnostic.

## Verification, limits and handoff

- Budget used: **33/40 Lean attempts, 3/10 Rust runs, 0 Kani**. Lean 29 pass / 4 fail; Rust 1 pass / 2 fail. L019 was a namespace/st0 unfolding error; L021/L022 were dependent array conversion proof errors; L030 was an explicit quotient-equality rewrite error. Their failed prints containing sorryAx are rejected evidence; all final modules compile cleanly with standard axioms only. No timeout or memory-killed run, cap increase or unchanged regression rerun occurred.
- Each attempt's exact target/command, source revision/hash, selected direct object/sidecar hashes, exit, wall time, RSS, swap, cgroup limits and full axioms/error log are in SDX_L*/receipt.json and SDX_R*/receipt.json with stdout/time/source snapshots. Lean aggregate wall 115.981818 s; peak RSS 4,098,112 KiB; swaps 0. Rust R003 wall 2.164506 s, peak RSS 230,492 KiB, swaps 0. Admission required allowed=true **and** exit 0 for each scope launch; no refusals/retries were encountered.
- Reused evidence: coherent SInt2 library/candidate objects and their manifests; pinned producer/provenance and raw elaboration failure packets; XRp's prior obstruction is corroborated, not replayed. No full frozen manifest, root release replay, extraction or SBF build was run. Final axioms audit is SDX_L033, not a new complete release audit.
- No shipped file or cfg(kani) harness changed. Three ELF hashes are **inherited, not freshly rebuilt**: default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`; devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`; Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.
- All edits are SDX-prefixed modules and this evidence directory. Session A worktrees/candidates and keys were untouched. Commits remain local; no push/merge. Owned host build outputs (90 files, 84,223,845 bytes) were hashed then removed (`SDX_cleanup.json`); receipt/source material retained.

The exact remaining deliverable is an owner-scoped resolution of the raw missing-write translation and the mutable restoration/from_fn ABI association, then a legitimate A2 equality or an explicit report that the intended equality must change. This packet makes no such change. S2 and the 100-bit release target remain not established.
