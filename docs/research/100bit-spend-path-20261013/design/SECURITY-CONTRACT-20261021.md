# Security contract (binding), 2026-10-21

This note reconciles the completion criterion used by every session. It
supersedes any shorter wording in other notes, including the lead's port
adoption addendum in `C3-BIN-20261021.md` (see the correction below).

## The user's target (recorded 15 October; reaffirmed 21 October)

From `TARGET-CLARIFICATION-20261015.md`: **"100-bit per-attempt soundness,
without grinding credit."** On 21 October the user added that the goal is
**classical security in the same units as Zcash's quoted 126 bits**, with
repeated attempts properly accounted for and no grinding credit or
work-normalisation tricks.

Operationally, completion means both of the following, proved for the
deployed verifier:

**(A) Per-attempt error.** One transcript attempt under the protocol's
challenge experiment fails, meaning a false statement is accepted, with
probability ≤ 2^-100. No proof-of-work bits count toward this, and no
probability is divided by adversarial work.

**(B) Repeated and adaptive attempts, stated plainly.** For an adversary
issuing at most Q oracle queries, counting repeats, the total failure
probability is bounded by an explicit expression that keeps its Q-dependence,
of the form (attempt starts) × B + collision mass. In particular, for an
adversary that makes no queries of its own and submits a single proof, the
bound must itself be ≤ 2^-100, which is (A) at the level of the whole
experiment. The bound must not be restated as a per-query rate in place of (B).

The Zcash comparison follows from (A) and (B) together. An attack doing W
hash evaluations succeeds with probability at most about W·B, so the attack
work needed for success probability near 1 is about 1/B ≈ 2^105. That is a
consequence used for communication, not the completion criterion.

## Where each endpoint stands against the contract

| Endpoint | Per-attempt mass B | Bound with no adversary queries | (A) | (B) |
|---|---|---|---|---|
| `R1FinalSoundnessHeadlineV3` (pure decision) | 15/2^109 ≈ 2^-105.09 | (0+34)·B + κ ≈ 0.996·2^-100 | met | stated |
| `OraclePortHeadlineFrozen` (adopted port) | 15/2^109 ≈ 2^-105.09 | (0+1080)·B ≈ 2^-95.0 | **not met** at the whole-experiment level | stated, with Q+1080 |
| `OraclePortHeadlineFrozenPerAttempt` (probability-level repair) | 15/2^109 ≈ 2^-105.09 | 34·B + κ(1161) + 2^-126 + 2^-454 ≤ 2^-100 | **met, conditional** | stated, with Q+34 for every Q |
| `OraclePortHeadlineFrozen2PerAttempt` (two-transaction checkpoint model) | 15/2^109 ≈ 2^-105.09 | 34·B + κ(1161) + 2^-126 + 2^-454 ≤ 2^-100 | **met, conditional** | stated, with Q+34 for every Q |

All four are conditional on their source premises. None is release-complete
for the deployed verifier until those are discharged. In particular, the single-pass `OraclePortHeadlineFrozenPerAttempt`
endpoint retains exactly `hqueries`, `AcceptedRunJoin D rust` and
`StoredCarrierBinding D rust P runtime`; its premise signature diff is empty.

The port's 1080 counts verifier-issued terminal Merkle reads as potential
attempt starts. This is a counting artefact of the union bound, not an attack.
A compiled counterexample (`ROWAWARE-DRAFT-20261021.md`) shows that such a
read can be recognised as a fresh start by the decoder, so the decoder-level
fix failed. The probability-level repair is proved in
[`START-CHARGE-20261021.md`](START-CHARGE-20261021.md): the submitted
transcript's starts are already read in the prover/sampler prefix, before
terminal authentication. The restricted hit event has mass at most
(Q+34)·B under the unchanged full adaptive experiment. The collision mass
κ(Q+1161), extractor abort 2^-126, and query-scan exhaustion 2^-454 remain
unchanged. `OraclePortHeadlineFrozenPerAttempt.failure_bound` states their
full sum for every Q; `zero_queries` proves (A) at the whole-experiment
level. `per_query` retains the old Qmax with no positive lower bound on Q.
No decoder, shipped implementation, security metric or adversary restriction
changes. The old adopted endpoint itself remains unchanged.

## Correction to the lead's adoption addendum

The C3-BIN addendum "oracle-decision port ADOPTED" (2026-10-21 09:40) gave the
target as "(Q+1)/2^100". That is a corollary, not the contract, and under the
port it holds only for 32 ≤ Q ≤ Qmax. The binding criterion is (A) and (B)
above. The unchanged `OraclePortHeadlineFrozen` endpoint must not be described as
meeting 100-bit per-attempt soundness. `OraclePortHeadlineFrozenPerAttempt` provides
the conditional single-pass probability repair; correspondence to the deployed verifier
and the runtime carrier binding remain outstanding.


## Two-transaction model target

The additive `OraclePortHeadlineFrozen2PerAttempt.final_soundness` targets
`OraclePortFrozen2.dV_frozen2`, including checkpoint save and authenticated
resume between batch 0 and batch 1. Its source premise is the newly targeted
`OraclePortFrozen2Join.AcceptedRunJoin D rust`; it retains the original
`StoredCarrierBinding D rust P runtime` and adversary query-count hypothesis.
Boolean acceptance equivalence does not convert the old single-pass source
join into this new ordered-log join. The old endpoints remain separately
named historical model theorems.

The verifier envelope remains 1161: a symbolic one-resource-per-slot
improvement pays for the six extra checkpoint digest reads. First reads
remain at most Q+1161, and the recorded log is at most Q+2322. Submitted
transcript starts are already followed in the prover/sampler prefix, before
all checkpoint digests, so the start charge remains Q+34. Digest inputs need
not be syntactically disjoint from the decoder language.

`failure_bound` states the full repeated/adaptive-attempt expression, and
`zero_queries` proves the whole-experiment ≤2^-100 inequality. The extractor,
B, collision function, abort allowances, query range, adversary and security
metric are unchanged. See [DV-TWOTX-20261021.md](DV-TWOTX-20261021.md) and
the receipts under `evidence/dv-twotx-20261021/`. This is a conditional model
endpoint. The deployed security target is **not yet established**: the new
frozen-source accepted-run join and runtime/carrier binding remain open.

## Owner-approved amendment, 2026-10-26

The owner approved three changes on 2026-10-26. The target, metric, failure event and numerical constants are UNCHANGED: 100-bit per-attempt soundness without grinding credit; zero-query whole-experiment bound at most 2^-100; repeated attempts stated as (Q+34)·B plus collision terms.

1. **Headline model is frozen3.** The model headline moves from `OraclePortHeadlineFrozen2PerAttempt` over `dV_frozen2` to its frozen3 counterpart, over the complete frozen3 verifier (`F3_Model`). frozen3 keeps frozen2's sampler-first schedule and adds a distinct physical public carrier (the 1880-byte ASF8 statement), used by checkpoint write/resume. Reason: the deployed source hashes the physical public bytes at checkpoint, which frozen2 did not model, so frozen2's exact log join (L157) is false for the deployed code (design/LOG-ALIGNMENT-20261026.md). Evidence: `F3S_Join.accepted_log_eq` and the F3T_ bounds (Q+34 starts, Q+1161 distinct reads, Q+2322 issued calls; exact zero-query margin 2^-108 − 6(1161²+2965²)/2^256 − 2^-126 − 2^-454 > 0). The replacement for L157 is "raw canonical join OR the charged collision event"; the collision branch is charged in the bound.

2. **Game statement for the two-transaction spend.** The experiment is the deployed two-transaction spend executed by the Solana runtime:
   (a) the TX1 and TX2 entries are consecutive executions on one bank lineage;
   (b) both name the same physical verifier checkpoint (CP) account, and no other transaction touches that account between them;
   (c) TX1's final parent status is success;
   (d) the recorded checkpoint actions are the physical runtime actions of these two transactions.
   This states the game the contract always intended ("checkpoint save and authenticated resume between batch 0 and batch 1"); it is not an assumption about attacker behaviour. The attacker remains adaptive and chooses both submissions.

3. **New named runtime trust item: RuntimePersistence.** `CPR_DataPersistence.TwoTransactionLaw` (design/RUNTIME-PERSISTENCE-ITEM-20261026.md). For the next transaction that loads an ordinary account (not fee payer, not durable nonce) on the same bank lineage, the loaded data bytes are the previous transaction's final bytes if its final parent status was success, and its starting bytes otherwise. Zero lamports means absent. The item covers data bytes only: no owner, balance, privilege, SDK or verifier claim. It reflects documented Solana transaction-pipeline behaviour and the Agave account loader, and joins the existing runtime trust items (RuntimeEntrypointAdmission, RuntimeSyscall, Allocator).

## Owner-approved amendment, 2026-10-27

The owner approved all three open recommendations on 2026-10-27 ("do your
recommendations for all open qs"). The target, metric, failure event, work
metric and numerical constants are UNCHANGED: 100-bit classical per-attempt
soundness without grinding credit; the zero-query whole-experiment bound at most
2^-100; repeated attempts stated as (Q+34)·B plus the collision terms; the exact
zero-query margin 2^-108 − 6(1161²+2965²)/2^256 − 2^-126 − 2^-454 > 0.

1. **Headline statement is `AspisR1.ARX_Root.deployed`.** It replaces
   `AspisR1.Rc10_Top.deployed` as the adopted top. The only binder changes:
   the independently supplied ByteProver `P`, `runtime` and
   `binding : StoredCarrierBinding …` are replaced by an arbitrary account
   adversary `a : SCE_Experiment.Adversary A`, with `P` the prover induced by
   `a` (`ARW_Induced.program`) and `runtime` the admitted runtime image
   `ARX_AdmittedRuntime.runtime`; the query budget bounds `a`'s issued digest
   queries across both reached phases (`ARW_Induced.issued`, identified with
   `(eval H P).1.length` by `ARW_Induced.queries`), counting duplicates and
   rejecting prefixes. The adversary is arbitrary and fully adaptive. The
   admitted runtime's world range is exactly the executions the approved game
   admits (each with its own `ARU_Support.At` witness); outside it the security
   mean is zero-extended with the original oracle weights, never conditioned.
   All other binders, carriers, the collision event at Q+2965, the bound
   `F3T_Numeric.total Q`, its range and the conclusion are literal to Rc10.
   Evidence: `ARX_Root.deployed` (account-rejoin9, 680b10c65d), fresh compile
   on the coherent cohort with axioms propext/Classical.choice/Quot.sound only
   (replay-dry9 RPz8_), conservativity on the old pure-choice class
   (`ARX_Conservativity.conservativity`). Full text:
   [ARX amendment](../../../../design/SECURITY-CONTRACT-ARX-AMENDMENT-DRAFT-20261027.md),
   before/after kernel statements in evidence/recount11-20261027/ and
   evidence/replay-dry9-20261027/. This removes L159/L185 and L181 from the
   ledger; it does not establish source-to-ELF correspondence, L166, L188 or
   joint non-vacuity.

2. **D188 is read at trace fidelity.** We trust the pinned Charon/Aeneas
   translation of each specifically associated shipped Rust body to preserve
   both the accepted Result and the chronological attempted digest-call
   sequence of its monadic extracted execution, including duplicates and every
   issued call before rejection; rejected prefixes must both reject, with
   differing non-Ok error kinds allowed (the recorded Err(Parse) versus
   extracted fail-panic discrepancy). The guarantee applies to the SAME body,
   inputs, digest replies and source/producer pins, not to an arbitrary
   recorder or caller. `S2W_DigestExtraction.AeneasExtraction.stage1`,
   `stage2` and `digestSource` keep their existing kernel types; no Lean axiom,
   compiler equivalence or opaque-body semantics is added. Non-extracted
   wrappers and unsafe construction still need the P6 route, and L166 must
   still be PROVED from the extracted trace and joined to its consumer; this
   wording closes no row by itself.

3. **Trust inventory recorded.** The one-to-one inventory of every trust
   surface in the adopted closure (44 named fields, definition-level and
   external surfaces) and the contract paragraphs for S2TrustedSdkBorrow,
   TrustedStd (slice copy and pure Option/Result), P1, the P6/Kani association,
   P7 (compiler, platform tools and the release-pinned library base), the
   standard logical axioms and the historical checkpoint interfaces are adopted
   as written in the
   [trust inventory appendix](../../../../design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md),
   with its trace-fidelity D188 column (item 2 above). Retained, not waived:
   - **W1:** `TrustedStd.slice_copy_from_slice` quantifies all abstract
     states; each actual use must have justified reference validity.
   - **F-AXIOM:** 105 nonstandard axioms are imported but unreachable from the
     adopted top; they are not security premises and remain a finding under the
     strict import-wide audit.
   - **D188-P2 caveat:** the selected PublicPreparation / ExtractedTx1Model /
     S1 semantic-prefix cohort models the retired `verifier.tx1` path at five
     interfaces (dot_type, prepared_claim, query_geometry, tx1, tx1_finish).
     The theorems are valid about their model; deployed attribution across the
     semantic-prefix/preparation/query/finish boundary is QUALIFIED until the
     association rows close against the frozen release source
     (design/D188-PROVENANCE-FINDING-20261027.md).

Not approved by this amendment: route A (translator upgrade and D188 re-pin),
any change to the target, constants or adversary, and any release claim. The
deployed security target is **not yet established**.

## Owner-approved amendment, 2026-10-27 (second): headline specialisation, query-bound classification, D188 narrowing

Approved by the owner on 2026-10-27 (owner message, verbatim: "i gpo with all your recommendations"). It
covers the lead's recommendations in HEADLINE-SPECIALISATION-DECISION-20261027.md,
D188-FIDELITY-DECISION-20261027.md and the closure status update. The target
(100-bit classical per-attempt security, no grinding credit), metric,
adversary, failure event, numeric bound and implementation are unchanged.

1. **Headline statement.** The soundness headline is stated for the installed
   configuration: `AspisR1.RPx_Deployed.deployed`. Its complete kernel
   statement is byte-identical to the reviewed `AspisR1.FJv_Deployed.deployed`
   (SHA-256 8ae0107f9dbb7374135912ff9dda3597ad0096023d0deed471b0cd4dcf305523;
   evidence/replay-deployed2-20261027/RPx_Deployed.kernel.lean.txt, compared
   with evidence/stack1-20261027/FJv_after_deployed.kernel.lean.txt). It fixes
   the configuration to `IDa_Deployed.deployedConfiguration missing indexError
   reservation`: installed finish, boundaries with terminal :=
   FIq_Terminal.terminal, and std. The six residual implementation inputs stay
   universally quantified, with no law. The proof differs from FJv_Deployed's
   only in one helper, restated over the pinned cohort's Phase carrier
   (evidence/replay-deployed2-20261027/RPx_HELPER_CHANGES.md).
2. **Query bound.** L154, the adversary's issued-query budget
   `issued ≤ Q0+Q1`, is classified as a parameter of the headline statement:
   the Q in the bound `(Q+1)·2^-100` on `Q ≤ F3U_RangeEdges.maxQueries`. It is
   no longer an open premise. This is a classification, not a discharge. The
   statement still quantifies over every adversary and charges every issued
   query, including duplicates and rejected prefixes. Campaigns of repeated
   attempts are accounted for by the per-attempt bound exactly as in the
   2026-10-21 contract.
3. **D188 narrowed.** D188 (the pinned Charon/Aeneas translation is the
   semantics of each translated shipped body, at trace fidelity) is narrowed
   to bodies that pass both a static scan for the dropped-restoration pattern
   and a native differential on inputs where their writes matter
   (D188-PROVENANCE-FINDING-20261027.md, finding D188-P3). Any translated body
   that fails, starting with `sampler::low_base_p_digits`, is treated as an
   opaque leaf. It needs a native P6 bridge from the frozen Rust to the cohort
   model the proofs use (owned reference, Kani, Lean model), exactly as the
   existing twelve opaque leaves do. Bodies that write through a mutable borrow
   obtained from an iterator or element accessor carry no D188 credit until
   checked. This shrinks the trust surface and adds no trust item.
4. **Client toolchain pin.** The native client build toolchain is pinned to
   rustc/cargo 1.94.1 (rustc commit e408947bfd200af42db322daf0fadfe7e26d3bd1,
   2026-03-25; cargo 29ea6fb6a, 2026-03-24), LLVM 21.1.8, host/target
   x86_64-unknown-linux-gnu, with the recorded RUSTFLAGS and no target-cpu
   change. It is to be recorded as a rust-toolchain file for the client build
   and in the release ledger, and re-confirmed at prover candidate adoption
   (LOG D270). The client release recipe's features and constant-time
   private-input decoding (LOG D272) are NOT covered by this approval.

Deployed 100-bit target: not yet established.

## Owner-approved amendment, 2026-10-27 (third): direct native bridges replace the emission route for verifier code

Approved by the owner on 2026-10-27 (owner message, verbatim: "yeah do that"),
in reply to the lead's proposal to extend the direct native-to-model bridge
method beyond the 13 opaque leaves. The lead read the message as approval of
the route change; the owner may narrow it.

1. **Route.** The correspondence between the adopted cohort models (the
   definitions the soundness proofs reason about) and the deployed code is
   established, for the verifier code on the reached TX1 and TX2 paths, by
   DIRECT hybrid native/Kani/Lean P6 bridges from the frozen Rust (revision
   4bb3b3f5...) to the cohort definition. This is the method of the 13 CLOSED
   opaque leaves (C3-BIN shared P6 method, Lean-discharged field stubs,
   loop-iteration rulings). A bridged function needs neither D188 credit nor
   any library model.
2. **What it replaces.** For bridged functions, the association rows A0-A8
   (cohort equals emitted kit) are no longer required. D188 and the A-rows
   stay available for any function the lead chooses not to bridge, under the
   narrowed D188 and the 23:00/23:10 UTC kit-method rulings; no credit is
   taken from them until they close.
3. **Composition.** Bridges compose by the call structure of the frozen
   source: a caller's bridge cites its callees' CLOSED bridges, and every
   callee use must lie within that callee's stated domain. The domain each
   caller establishes is proved, never assumed.
4. **Unchanged.** The 100-bit classical per-attempt target, metric,
   adversary, failure event and numeric bound; the headline
   RPx_Deployed.deployed and L154's classification; frozen3,
   RuntimePersistence and the game; the implementation and release pins. The
   source-to-ELF audit (L188) is still required: native bridges are about the
   frozen Rust source as compiled by the pinned toolchain for the Kani
   harnesses, not about the deployed ELF bytes.

Deployed 100-bit target: not yet established.

## Owner-approved amendment, 2026-10-28 (fourth)

Owner message, 2026-10-28 ~06:45 UTC: "i acceot yiour recommendations". This adopts the lead's two open recommendations.

1. Kani trust narrowing (finding K-1, KANI-FIDELITY-FINDING-20261028.md). A Kani result counts as evidence only for a harness that either reaches no copy builtin, or runs with exactly the validated KMX_ element-wise copy stubs (KMX_copy_stubs.patch, sha256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67) and has its matched negative control fail in the identical configuration (lead ruling (r'), shared with Stream B). A timeout gives no credit. This narrows the existing Kani trust row; it adds no new trust item and changes no security bound, metric or game.
2. One aggregation scope above the standing 8 GiB cap. A single job on the build host: MemoryMax 16G, MemoryHigh 14G, MemorySwapMax 0, Lean -M15000, one run, recording target, exit status, wall time, peak RSS, swap, source revision and #print axioms. Its only target is JHn_TX1.accepted1_saved, the join of the two separately compiled halves, which failed at import at 7.27 GB under -M7000 (AGENTS resource rule 4, legitimate final aggregation). The same scope may be reused for the later TX1+TX2 joint assembly, recorded the same way. It may not be reused for any reduction-shaped failure; those are split.

Deployed 100-bit target: not yet established.

## Owner-approved amendment, 2026-10-28 (fifth)

Owner message, 2026-10-28 evening: "take all your recommendatrions". This adopts the lead's recommendations in design/COMPOSITION-TRUST-DECISION-20261028.md and design/STRATEGY-CHECKPOINT-20261028.md:

1. **Composition trust, option A.** "Native contract semantic transport (result projection)" is recorded as an EXPLICIT CLARIFICATION of the existing P6 (Kani) and D188 (Aeneas) tool trust, not as a new kind of trust. It is scoped to the enumerated bodies, references, dictionaries, features, encodings and tool versions in the accepted receipts; its row text is the NCQ_ draft quoted in the decision document. When native contracts and Lean reference proofs replace parts of the `extraction` premise, this is reported as a RECLASSIFICATION (an unchecked algorithmic claim replaced by checked evidence plus this narrow tool-agreement row), never as a premise removed by proof.
2. **FixturePdaRuntime: deferred.** It is not adopted. It stays a named hypothesis of the fixture-only TX2 non-vacuity theorems until the lead brings it back with the decoders complete.
3. **Two routes in parallel.** (A) Release route: finish the bounded deployment items (joint real-byte non-vacuity, L186/L188 source-to-ELF and final trust/axiom audit, S10 completeness), so that the release statement reads "machine-checked for the deployed program, conditional on the explicit owner-accepted trust inventory". (B) Trust-reduction route: continue native bridging, using Kani contracts where the pinned tool supports them and a written, audited call-graph composition argument elsewhere.
4. **Newer Kani: sandbox evaluation only.** A newer Kani release may be evaluated outside the pinned release configuration, for contract support on slice and Vec returns and for loop contracts. Adoption needs a further owner decision, after the K-1, K-2 and contract fidelity controls have been re-run on it.

Deployed 100-bit target: not yet established.

## Owner delegation, 2026-10-28 evening (standing)

Owner message: "ultimately you can take authority as long as you dont compromise 100 bit soundness, privacy and 2 tx, anything else is your call. no work normalised soundness".

Standing delegation to the soundness lead. The lead may decide method, tooling, trust-boundary clarifications, routes, scheduling and resource matters WITHOUT further owner approval, PROVIDED the decision does not compromise:
1. the 100-bit soundness target for the actual deployed spend path, PER ATTEMPT, with NO work-normalised soundness and NO grinding or proof-of-work credit (as stated in AGENTS.md; this restates the target, it does not change it);
2. privacy (Stream B's contract, including the side-channel scope of D159);
3. the two-transaction design (the approved two-transaction game, RuntimePersistence).
Any change that would weaken any of these three still goes to the owner. Every decision taken under this delegation is recorded in C3-BIN with its reasoning, and in the trust inventory if it touches trust, and is reported to the owner in plain language.

## Owner approval, 2026-10-29: deploy the release verifier to devnet

Owner message: "approved", in reply to the lead's recommendation to deploy the release devnet verifier (ELF 63ad3e9c..., built from frozen source 4bb3b3f5... with the devnet Pool/registry IDs) as a NEW immutable devnet program (the existing verifier Gk16sp... is immutable and runs the historical fb2fc048...), wire it into the registry and Pool through their normal instructions, and re-run the read-only chain association (L188 obligation 5). Scope: devnet only; no mainnet. Conditions set by the lead: a full rehearsal on a local test validator with cloned devnet accounts first; the exact commands reviewed by the lead before any devnet write; no protocol or source change (if wiring would need a code change, it goes back to the owner).
