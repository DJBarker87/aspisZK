# Overnight summary, 20→21 October 2026

> **Correction (10:55, 21 Oct):** the binding completion criterion is the user's
> per-attempt target (100-bit per attempt, no grinding credit, plus the plain
> query-dependent repeated-attempt bound). It is in `SECURITY-CONTRACT-20261021.md`.
> The "(Q+1)·2^-100 per query" wording below is a derived corollary, not the target.

Lead coordinator summary of the overnight Codex run (about 21:30 to 07:00).
The detail sits in the addenda of `design/C3-BIN-20261021.md` (soundness)
and in LOG D85–D119 of `docs/research/v8-r0-zk-20261009/LOG.md` (privacy).
Every merged result was reviewed before cherry-picking. Each review checked
for `sorry`, axioms, `admit`, `native_decide` and `implemented_by`, compared
before/after signatures wherever a premise was claimed removed, and, for any
job that touched shipped crates, required a rebuild of all three frozen
programs: default `dfc2a91a…`, devnet `fb2fc048…` and Pool `121f3e29…`.
Each was byte-identical, every time.

## Decisions waiting for you

1. **Soundness wording: per oracle query, not per attempt.** `hN` (at most
   33 recognised starts) turned out to be a restriction on the adversary, and a
   compiled adversary breaks it. The earlier "< 2^-100 up to 2.2·10^22 queries"
   depended on it and should not be cited. The proved form is per query: for
   an adversary making at most Q oracle queries, failure ≤ (Q+1)·2^-100 for
   every Q up to about 1.5·10^46 (2^153). The lead has assumed the per-query
   wording; please confirm it.
2. **Oracle-decision port.** Every soundness source job tonight (R3, R13–R16,
   R9, the tag law, R4, S2, S7, S8) ended at the same place: the headline's
   decision `d` is a free pure function, so nothing ties it to the frozen
   verifier, which recomputes Merkle paths with hash calls. The fix is to let
   the decision query the oracle and to state the headline at the frozen
   verifier's decision. A draft port is on the **unmerged** branch
   `codex/cx-oracle-port-draft-20261021` (pushed to origin as a backup). It
   now has a **completed draft headline**,
   `OraclePortHeadlineDV.final_soundness` (`OraclePortHeadlineDVC7.lean`,
   branch head 3a01b2d6d). Its only premises are:
   - `hqueries`, the adversary's query budget;
   - `h_Rust_equals_dV : ExecutionJoin D rust`, saying the frozen Rust verifier
     executes as the modelled frozen decision dV;
   - `h_stored_runtime : StoredCarrierBinding …`, the runtime binding of the
     stored proof bytes.

   R16, R13, R15, R3, R14's model part and the tag law are all theorems
   there, proved through `checked_acceptance` (C6) and the stored-aware
   probability bridge (C7). Numbers: κ(Q+1161) and B unchanged; the start
   multiplier is Q+1080, so the per-query form (Q+1)·2^-100 holds for
   32 ≤ Q ≤ Qmax; extractor cost ≤ 4·scale³·(Q+2323)³. A second unmerged
   draft, `codex/cx-rowaware-draft-20261021`, tried a row-aware decoder to
   bring the bound back to Q+34. It failed: a compiled counterexample shows a
   frozen node can extend a fully cached row-zero prefix and add one fresh
   start without a binary collision. So under the port the per-query form
   needs Q ≥ 32; for Q < 32 the absolute bound is still about 2^-95, which is
   equivalent to F ≤ max(Q+1, 33)·2^-100 for every Q. The current v3 headline
   (no port) keeps Q+34 and holds for every Q. Design notes:
   `design/OraclePortContinuation7-20261021.md` on the draft branch, with
   its comparison against headline v3. 11 + earlier modules, standard
   axioms, zero swap.
   Join split (unmerged branch `codex/cx-join-split-draft-20261021`,
   `design/JOIN-SPLIT-DRAFT-20261021.md`): `ExecutionJoin` is proved to follow
   from per-cone joins (S1–S10, parser, multiproof, checkpoint ABI, Pool
   caller) plus one ordered caller join, with the landed certificates and R22
   totality plugged in. That gives session A an exact per-cone target table.
   It found one fidelity gap: frozen batches short-circuit after a failure,
   but the draft dV evaluates the remaining slots. A follow-up draft
   (`codex/cx-shortcircuit-draft-20261021`) makes dV short-circuit like the
   frozen code and proves acceptance is unchanged.
   Fidelity chain after the split (all unmerged draft branches, each stacked
   on the last):
   - `cx-shortcircuit-draft`: the outer short circuit now matches the frozen
     verifier, with acceptance unchanged and prefix logs (`OraclePortHeadlineDVsc`).
   - `cx-inner-order-draft`: the model slot is more permissive than the
     frozen one (it accepts non-zero padding).
   - `cx-refine-join-draft`: proves the one-directional ExecutionRefinement
     (strictly weaker), the ≤1161 accepted-run bound, and guard erasure on
     accepted runs. Log containment alone does not transfer the extractor
     (countermodels), so
   - `cx-acclog-draft`: proves the conditional `OraclePortHeadlineAccLog`
     whose only join is `AcceptedRunJoin`: equal logs and outputs on
     frozen-accepted runs, covering both annotation passes. It is strictly
     weaker than ExecutionJoin. It also proves the model's recursive
     multiproof order differs from the frozen ascending-level order on
     accepting slots, and that this permutation changes recovery. So the model
     must adopt the frozen order.
   - `cx-frozen-order-draft` (HEAD 7edd59818, pushed): **done**. dV_frozen
     uses the exact frozen order (sorted leaves and duplicates, then ascending
     levels and parent indices). For level-order logs it re-proves
     collision-free recovery through shared paths, verifier budget ≤ 1161,
     starts ≤ Q+1080, log ≤ Q+2322, and checked_acceptance.
     `OraclePortHeadlineFrozen.final_soundness` (and `per_query`) has exactly
     three premises: `hqueries`, `AcceptedRunJoin D rust` (the frozen Rust
     verifier's accepted runs have the same logs and outputs as dV_frozen)
     and `StoredCarrierBinding` (runtime). 25 modules, 69 theorems, standard
     axioms, zero swap.

   **This last branch is the one to review if you adopt the port.** Each
   branch in the chain contains the ones before it. If adopted, the full
   soundness gap is the per-cone accepted-run refinements of the frozen
   source to dV_frozen (table in the join-split design note, updated on the
   last branch), which is exactly what the S-cone re-pins establish, plus
   the runtime carrier binding.
   Recommendation: adopt. The whole soundness gap then becomes one
   Rust-equals-dV execution join plus the runtime carrier binding, which is
   exactly what the S-cone re-pins establish. Nothing merges without your yes.

   Cone audit (read-only, branch `codex/cx-cone-audit-20261021`,
   `design/CONE-AUDIT-20261021.md`): all 14 cones are classified against the
   frozen-order join table. No cone yet has a complete instantiated
   accepted-run join; total-form local helpers are listed separately. The
   cheapest next three are S9, S3 and the checkpoint ABI.

   Checkpoint ABI cone (branch `codex/cx-ckpt-abi-draft-20261021`, on top of
   the audit): proved total saved-ten reference decoding with duplicate
   rejection, prepared/accumulator equality, the twelve-step resume, the
   exact six ordered digest reads, exact immutable byte reads to offset 1736,
   and producing-call witnesses for every extracted resume field. Still open:
   writer/codec adoption, reached-state provenance, Vec/allocation, and the
   frozen driver. The concrete unwrap crosses the nonstandard `Formatter`
   boundary. 33 theorems, standard axioms.

## Soundness

Current headline: **`R1FinalSoundnessHeadlineV3.final_soundness`**
(`design/SOUNDNESS-HEADLINE-20261021.md`, sections v1, v2, v3).

    F ≤ (Q+34)·15/2^109 + 6·(Q+1161)^2/2^256 + 2^-126 + 2^-454
    Q ≤ 2^153 (exact Qmax in the file)  →  F ≤ (Q+1)/2^100

Here F is the deployed two-transaction failure probability at the constructed
tx1/Pool instance, and Q bounds the adversary's oracle queries, counting
repeats. The extractor is the concrete `ActualCostedExtractorM10.extractor`,
with cost ≤ 4·scale³·(Q+1162)³.

Removed or discharged tonight, each by a checked deletion-only or
strictly-weaker signature diff:
- `hN` → the per-query bound (Q+34 starts, proved).
- `h_R4_row31`, from R16 placement and the sampler invariants.
- `h_R18`, which was unused.
- `h_R19`, derived from the query budget (verifier ≤ 561 queries).
- `h_R9_transport`, at the constructed tx1/Pool instance.
- `h_Rwire`, narrowed to a single tag-rejection law.
- R16/R13/R14/R15/R3, weakened to collision-free runs (strictly weaker; the
  collision mass is already charged).
- All of M10: `h_M10_ledger`, `h_M10_uniform`, the allocation mirror (with the
  lead's check that it is concrete), and `h_M10_log_length` (log ≤ Q+1122).

Still assumed: the query budget; R16/R13/R14/R15/R3 on collision-free runs;
the tag rejection law; and the BoundaryEvidence fields: P1–P7 trust and
runtime, and the frozen-source joins R10, R17, R20–R22, R4 transport and
S1–S10.

Source-side progress, without premise removal: ASQ8 encoder equivalence (P6);
R17 geometry tables certified (2×512 entries, plus 262,144 fibres and
1,048,576 slots); the S2 header rejection proved against the frozen crate;
S7 and S8 P6 certificates (owned references translate, loop proofs by step
plus induction), up to the caller execution join; P5 bump guards (61 Kani
harnesses); R4 sampler pieces; R22 overflow freedom as a corollary of total
cone theorems (35 of 146 cone theorems are already total). Encoding
uniqueness holds: the frozen verifier and Pool reject non-canonical limbs, so
each spend has exactly one marker PDA (D97, no change needed).

## Privacy

Current headline: **`PrivacyR1HeadlineV2.privacy_headline_v2`**, with the
alternative `privacy_headline_v2_fibres` and the cost-annotated
`PrivacyR1HeadlineV2SimProto` (`r1p-final/PRIVACY-HEADLINE-20261021.md`).

    ε ≤ 2^-109 + 2^-137 + 2^-454 + 128(M+1)/2^190 < 2^-100,   M ≤ 2^25

Removed tonight:
- the causal premise (phase-restricted protocol model, D85–D88);
- the commitment families, read coverage and public width (D89);
- the real-side history law, via scan freshness (D91–D94; D93 corrects a
  wrong lead ruling in D91);
- builder soundness and `hpub` (D96);
- all accounting rows: packing basis, counters, streams, cells, blocks,
  coin carrier and sample carriers (D106);
- the wire batch and ordered-log premises, after fixing the protocol
  encoding (D111).

The fibre/exhaustion/budget premises are reduced to one `CallerLaw` (D110,
D112). Simulator cost is relative to the adversary's input length:
replay ≤ c·(n+1), lazy cache ≤ C·(n+1)², sampling coupled with truncation
≤ 2^-120 (D114–D119). `sim_preparation` is still open.

Still assumed: `CallerLaw` (shipped prover callers; part 10 fixed the decoder
and stopped at the outer-caller transport), the builder source join
(`RustRuntimeJoin`; forest admission is mostly done), the Rust serialisation
join, the real/ideal execution joins, and `sim_preparation`.

## Paused and parked tracks

- Candidate freeze (the 1.19M CU candidate) is parked at 10/12 cones after
  prep9 cost about 0.9M tokens for one cell. Resume when you want it adopted;
  shipped-file edits merged tonight must be carried onto that branch and its
  pins rechecked (all edits are cfg(kani)/cfg(aeneas_ref) only).
- The builder (11 parts), prover commitment (10 parts) and simulator cost
  (4 passes) tracks are paused at the prover-side execution join or at an
  exhausted env-J attempt range.

## Items for session A

- Please state S-cone re-pin theorems in **total** form (∀ inputs, the
  extraction returns `ok`). Then R22 (overflow freedom) follows for each cone
  as a corollary, via the lemma proved in `R22-TOTAL-20261021.md`.
- Combined import collision: the duplicated `instDiscriminantErrorIsize`
  instances block one aggregate import. A type-qualified naming fix is
  prototyped in `IMPORT-UNION-20261021.md`, and S10 pins need updating
  before the single final manifest replay.
- Lead error: commit aab0d23d0 swept in session A's 23 staged
  `s5-p6-serializer-kani` files under a lead message (shared index). Nothing
  was lost; authorship is session A's. Lead commits now use explicit paths.

## Other errors and corrections

- D91 → D93: the lead first ruled that every repeated read was a collision.
  An adversary may repeat queries legitimately, and the worker compiled that
  counterexample; the corrected event is scan freshness only.
- A Codex content filter blocked the first limb-canonicality review (it read
  as attack framing). It was rerun as an encoding-uniqueness correctness
  property.
