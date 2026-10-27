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
