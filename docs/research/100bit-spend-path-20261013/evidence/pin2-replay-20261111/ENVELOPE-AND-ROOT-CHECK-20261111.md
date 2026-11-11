# Envelope composition and source-root binding check (2026-11-11)

Read-only source review of the `research` checkout (/Users/dominic/ZK) and the pin `c7593d23fdc`, read with `git show`. Nothing was compiled or run.

Path note: the R1_SOUNDNESS.md cited in the brief is at docs/research/v8-r1-20261011/R1_SOUNDNESS.md:364-366, not under 100bit-spend-path-20261013/design/.

## Question 1. Is the start charge N·B uniform or a per-row sum?

**Answer: uniform by construction.** Every route that produces the start charge is a count multiplied by one scalar density. No Lean lemma in the tree gives an adaptive per-row (sum of row caps) first-read bound.

### The chain that produces (Q+34)·B in the headline total

1. Headline. evidence/host-ids-20261110/NPO_FinalB.lean:112-116 ends in `≤ F3T_Numeric.total (fx.Q0+fx.Q1)`.

2. The numeric total. evidence/frozen3-head-20261026/F3T_004/sources/F3T_Numeric.lean:11-13:
   ```
   def total (Q : Nat) : Rat :=
     ((Q+34 : Nat) : Rat)*PerAttemptEnvelope.B + collisionLoss Q + accountLoss Q +
       1/(2:Rat)^126 + 1/(2:Rat)^454
   ```

3. The probability bound. docs/research/100bit-spend-path-20261013/lean/Frozen2StartChargeProbability.lean:29-36. StartChargeProbability.lean:29-36 is identical.
   ```
   theorem restricted_union_bound (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
       (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
       lazyMean (projected D P) emptyTable (fun run => indicator (prefixHit D P run)) ≤
         ((Q+34 : Nat) : ℚ)*PerAttemptEnvelope.B := by
     rw [hit_mass]
     exact RawAdaptiveClassifierStartBound.shared_hit_mass_le_starts
       RawFullPublicSelection.select LiteralTableWordChoiceBin.choose (charged D P) (Q+34)
       (starts D P Q hq)
   ```

4. The scalar instantiation. lean/RawAdaptiveClassifierStartBound.lean:18-36:
   ```
   theorem shared_hit_mass_le_starts ... (exp : Program Bytes State (Pf × Bool)) (N : Nat)
       (hN : ∀ H, decoderFirstReads (RawAdaptiveLiteralDecoder.decode pubChoice words)
           emptyTable (eval H exp).1 ≤ N) :
       lazyMean exp emptyTable (fun run => indicator (hitsChain3 ... classifier emptyTable run.1))
         ≤ (N : ℚ) * PerAttemptEnvelope.B := by
     apply decoded_first_read_bound ... classifier PerAttemptEnvelope.B exp emptyTable N
   ```

5. The generic lemma. It takes one scalar `ε`. lean/DecodedFirstReadUnionBound.lean:29-35:
   ```
   theorem decoded_first_read_bound ... (dec : Dec X M C I A Y) (bad : ...)
       (ε : ℚ) (q : Program I A (Pf × Bool)) (t : Table I A) (N : Nat) (hε : 0 ≤ ε)
       (hbad : ∀ (a : I) (T : Table I A) own pend g, dec a T = some (own, pend, g) →
         blaw g (fun out => indicator (bad out.1 out.2.1 T out.2.2)) own pend ≤ ε)
       (hN : DecoderReadsBound dec q t N) :
       lazyMean q t (fun v => indicator (hitsChain3 dec bad t v.1)) ≤ (N : ℚ) * ε
   ```
   `DecoderReadsBound` (lines 19-27) is an unweighted counter: each fresh decoder start costs 1. `lemmaA3` (docs/research/v8-r0-close-20261007/lean/R0C/V3/Gen.lean:64-70) has the same shape with `FirstReadsBound`.

6. Where the rows collapse to B. lean/RawAdaptiveClassifierHitDensity.lean:25-48 (`literal_decoded_classifier_le`) proves the `hbad` premise with right-hand side `PerAttemptEnvelope.B`. It does so through `RawUnifiedDecoder.decoded_bound ... PerAttemptEnvelope.B`, whose premise quantifies over every row `i < 33`, discharged by `(LiteralDecoderEnrichment.density ...).trans (LiteralBudgetEnvelope.row_le P.round hi)`. lean/LiteralBudgetEnvelope.lean:40-55:
   ```
   theorem row_le (i : Nat) (hi : i < 33) :
       LiteralClassifier.budget i ≤ PerAttemptEnvelope.B
   ```
   The per-row budgets `LiteralClassifier.budget i` exist. They are bounded by B and discarded at this step.

7. The count N = Q+34. Frozen2StartChargePrefix.lean:89-101 (`starts`) concludes `decoderFirstReads ... ≤ Q+34`. It is the sum of the prover's starts (`DecoderQueryAccounting.starts_le_queries`, at most Q) and `BinHonestQueryBudget.verifier_starts`.

8. The constant. lean/PerAttemptEnvelope.lean:17 has `def B : ℚ := 15 / (2^109 : ℚ)`. Line 54 has `theorem thirty_three_B_lt : (33 : ℚ) * B < 1 / (2^100 : ℚ)`.

The other routes are uniform as well:
- lean/UnifiedEventDensity.lean:186-196 and lean/UnifiedCausalBound.lean:19-32 both conclude `≤ (N : ℚ) * B` for a scalar `B`.
- `R0P.Mask.combined_fiat_shamirZ` (docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskFiatShamir.lean:123-140) and `R0C.V3.theorem43` (Gen.lean:251-258) conclude `(Qtot : ℚ) * maxErr rb.ε pr.r + κ Qtot`. `maxErr` (docs/research/v8-fs-generic-20261006/lean/FS/Statement.lean:232-233) is a maximum over rows, `(List.range r).foldr (fun i m => max (ε i) m) 0`, so this route also charges count × max.

### Cross-check of the sibling agent's readings

- **(a) Confirmed.** The start charge is `restricted_union_bound` → `shared_hit_mass_le_starts` → `decoded_first_read_bound` with `ε := PerAttemptEnvelope.B`. N counts fresh decoder starts: at most Q from the prover plus at most 34 from the verifier.
- **(b) Confirmed, with one correction.**
  - `AspisR1.UnifiedFiatShamir.soundness_bound` (lean/UnifiedFiatShamir.lean:23-48) takes `(hl : ∀ n < 33, p.lbl n = UnifiedLabels.label n)` and concludes `≤ (Qtot : ℚ) * maxErr rb.ε 33 + 3 * (Qtot : ℚ)^2 / (256^32 : ℚ)`. This is the earlier unified route. The headline `total` does not go through it.
  - The sampler special-cases rows 26 and 31. lean/R1UnifiedSampler.lean:59-65 reads `if j + 1 = 26 then DuplexSamplers.reseeded ... else if j + 1 = 31 then QuerySamplerBridge.sampler ...`. The lemmas `row_reseed` (:80) and `row_query` (:86) state the same.
  - **Correction:** `verifier_starts` is not fixed at 33. lean/BinHonestQueryBudget.lean:104-111 concludes `decoderFirstReads dec T (eval H (verifier D d pub pf)).1 ≤ 34`, proved from `rows_bound` (:82-87, `≤ ns.length + if 26 ∈ ns then 1 else 0`) at `List.range 33`. The row count is fixed at 33. The start count is 34, because `sampler_starts` (:28-33, `≤ 1 + if n = 26 then 1 else 0`) gives row 26 two starts.

### What charging each start its own row cap would take

An instantiation of existing lemmas cannot do it. Three pieces are needed:

1. **A new generic lemma.** It would be a weighted form of `decoded_first_read_bound` / `lemmaA3`, with:
   - `ε : I → Table I A → ℚ`, the cap of the row the decoder assigns at that start;
   - `hbad` stated with `ε a T`;
   - a weighted `DecoderReadsBound`, where each fresh start subtracts `ε a T` from a rational budget W;
   - the conclusion `≤ W`.

   The induction would follow the existing one. This is a new lemma. A per-kind form, `Q·max_k ε_k + Σ_k n_k ε_k`, would be a corollary of it. It is not present.

2. **A row-dependent density.** This is a row-indexed restatement of `literal_decoded_classifier_le` / `adaptive_decoded_classifier_le` that stops before `LiteralBudgetEnvelope.row_le`. The components exist (`LiteralDecoderEnrichment.density`, `LiteralClassifier.budget i`). There is a real obstacle: `RawUnifiedDecoder.decoded_bound` quantifies over all rows of the decoded prefix. The row has to be determined by the start's (address, table), or the weight must be the maximum over the rows a start can decode to.

3. **A new concrete budget theorem** to replace `starts` (Q+34). It must show that along every path, the verifier's fresh starts are charged at most Σ over its rows of `budget(row)`, counting row 26 twice. The prover's Q starts stay at max = B, because an adaptive prover can aim a fresh start at any row. Premise to prove: each fresh verifier start decodes to that sampler's own row. If the prover read the address first, the start is not fresh and is charged once, on the prover's side.

The only existing per-index sum is `AspisV8R19.CausalFirstHitUnionBound.mean_firstHit_union_le` (docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/CausalFirstHitUnionBound.lean:48-52):
```
mean (fun x => indicator (∃ i, bad i x)) ≤ ∑ i, bound i
```
It is a static union bound over a fixed `Fintype` index, with each index's probability given as a premise. It contains no adaptive fresh-read law, so it cannot replace the weighted lemma above.

### Arithmetic context

These figures are Python evaluations of the Lean definitions with exact rationals. They are not Lean results.
- `queryCap` (row 31) is 0.967·B. B is set by the query row.
- Row 0 is 0.443·B, row 1 is 0.111·B, the other semantic rows are each at most 0.006·B, and the circle rows are each `atom` ≈ 2^-124.
- The opening rows are each below 2^-199 and the rho row below 2^-119.
- The sum over rows 0..32 is about 1.58·B.
- Uniform accounting for 41 starts gives 41·B = 615/2^109, which exceeds 2^-100 = 512/2^109 before any other term.

Under per-row accounting with items 1-3 proved, the sibling design's Q=0 start term would be about (1.58·B + one more row-26 charge + the caps of the 7 added starts). Whether that meets 2^-100 depends on the rows the 7 added starts charge, which this review did not see. Under the current theorems the design cannot meet the criterion.

## Question 2. Is the source current root bound in the pinned two-transaction path?

**Answer: no exposure found.** TX2 rebuilds the 1,880-byte statement with `current_root := selected_lane.tree.root`, read from the PDA-authenticated, Pool-owned lane account. `resume` then requires the hash of those rebuilt bytes to equal the public-statement digest that TX1 stored in the checkpoint. An S' whose root differs from the Pool's root is rejected at TX2 with `Error::Checkpoint`. The binding comes from this digest check, not from the transcript.

### Evidence (pin c7593d23fdc)

1. The transcript omits the root. crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:2023-2025:
   > "The source sequence number and the source current root are still not serialized and not hashed here."

   `public_bytes` (:2026-2090) writes `source.next_pair_index` and `frontier(&mut out, &source.frontier)`, and not `current_root`. The sequence number is tied separately. crates/aspis-statement/src/pool_v1/pair_tree_profile.rs:455-457 (`validate_pool_v1_pair_live_snapshot_v1`) has `if snapshot.sequence != snapshot.next_pair_index { return Err(...SequenceIndexMismatch) }`.

2. TX1 hashes the whole uploaded statement into the checkpoint.
   - programs/r1-cost-probe/src/r1_pool_adapter_owned.rs:390 has `let statement = decode_public_statement_box(&public_data)?;` and :409 has `first_decoded(statement.semantic_public(), &public_data, ...)`.
   - These lead to crates/aspis-r1-cost-probe/src/candidate.rs:288, `checkpoint(&p, &a, proof, public_bytes, hash)`.
   - crates/aspis-r1-cost-probe/src/verifier.rs:329 has `out.extend_from_slice(&hash.digest(&[public]))`, which places checkpoint bytes 48..80 = H(all 1,880 uploaded bytes, `current_root` included).

3. TX2 rebuilds the statement from Pool state.
   - r1_pool_adapter_owned.rs:250 has `require_readonly_account(lane_account, pool_program)?`.
   - :302-317 decode the lane and check the PDA with `Pubkey::create_program_address(&[PAIR_FOREST_LANE_SEED, master, &[output_lane], &[selected_lane.bump]], pool_program)`.
   - :318-325:
     ```
     let live_snapshot = Box::new(PoolV1PairLiveSnapshotV1 {
         ... sequence: selected_lane.tree.next_leaf_index,
         next_pair_index: selected_lane.tree.next_leaf_index,
         current_root: selected_lane.tree.root,
         frontier: selected_lane.tree.frontier,
     });
     ```
   - :367-368 call `reconstruct_asq8_statement(&request, &authenticated, &scanned.candidate_afterstate)`.
   - programs/r1-cost-probe/src/r1_pool_adapter.rs:808-824 (`asq8_common`) sets `live_snapshot: *authenticated.live_snapshot`.
   - :945-947 and :1005-1006 confirm that the owned `stage1`/`stage2` are the dispatched entry points.

4. TX2 requires byte equality with TX1's statement.
   - r1_pool_adapter_owned.rs:431 has `let public_bytes = encode_pool_v1_pair_forest_terminal_statement_v1(&validated.statement)` and :436 has `verifier::tx2_authenticated(&public_bytes, ..., &checkpoint_data, ...)`.
   - These lead to candidate.rs:295, `resume(checkpoint, proof, public_bytes, Variant::S2, hash)?`.
   - verifier.rs:396:
     ```
     if bytes[16..48]!=hash.digest(&[proof])||bytes[48..80]!=hash.digest(&[public])||... {return Err(Error::Checkpoint);}
     ```

5. The Pool hands the verifier its own lane account and settles only on the verifier's result.
   - programs/aspis-pool/src/pair_forest.rs:1653-1654 decode the lane at `output_lane`, and :1655-1664 run `validate_pair_forest_request_accounts_v1`, which includes the lane PDA match at :1365-1371.
   - :1733-1745 call `verify(... lane_account ...)`.
   - programs/aspis-pool/src/pair_forest_dispatch.rs:322-337 pass the same `lane.key` read-only in the CPI.
   - pair_forest.rs:1749-1760 run `validate_authenticated_terminal_result_v1`. Its rebuilt statement (:1488-1500, `current_root: lane.tree.root`) is checked against the result's afterstate, nullifier and account ids (pair_forest_terminal.rs:557-575). The result carries no source snapshot, so the Pool's own check does not see the root. The root is enforced only in the verifier at item 4.
   - The deployed Pool feature set is `r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit` (evidence/devnet-frozen-20261109/NPC_pool1/pool1/time.log). That set excludes `pair-forest-direct-result-audit`, so the `#[cfg(not(...direct-result-audit))]` branch at :1749 is the one compiled in.

### What an attacker could do

Holding a valid proof for S, the attacker can upload S' differing only in `current_root` and run TX1. The proof still verifies, because the transcript does not depend on the root, and the checkpoint stores H(S'). TX2 rebuilds S with the Pool's actual `lane.tree.root`, H(S) ≠ H(S'), and `resume` returns `Error::Checkpoint` (verifier.rs:396). TX2 passes only when the uploaded root equals the Pool's stored root at TX2 time, so the attacker gains nothing.

The root's consistency with the stored frontier rests on the Pool's inductive write invariant. Under the deployed `*-invariant-audit` features it is not recomputed on this path (pair_forest.rs:629-633). The frontier itself is bound in the transcript and is part of the digest-checked bytes.

Residual items:
- The model and proof side must carry this binding through `resume`'s digest check. The transcript does not provide it.
- This is a source reading only. No execution check was run.

target not yet established
