# Checkpoint ABI pass 5

Base `30e4f18dbd541c5b2f9fa90afa9c1cab92fd21ba`, branch
`codex/cx-ckpt-abi5-20261021`. New Lean modules only. No shipped source,
protected candidate, sibling module, wallet/key or ELF modification.
No push or merge. Complete checkpoint source join remains open.

## Stage 1: short-circuit reference to the new checkpoint stage

`OraclePortCkptAbi5Stage.stage_observation` proves exact evaluation equality
between the saved-ten short-circuit reference (whose decoded result drives
twelve continuation steps) and `OraclePortCheckpointOracleC5.writeResume`.
It holds for every oracle world and arbitrary retained proof/public bytes,
with distinct queries. Both ordered address/answer log and returned state
are equal; all six reads, including repeats, are retained.

`reached_stage` specializes this equality to the actual
`OraclePortFrozen2.checkpoint`, constructing Context from p/i/v as that stage
does. It derives distinctness from `input p q tr = some i` and
`queries tr = some q`, without assuming final acceptance or a supplied
unique-query fact. These are **model/reference** hypotheses and results,
not Rust Prepared/Accumulator provenance or a source cone inhabitant.

Attempt 2 exits 0: 16.933184292 seconds, peak RSS 3,581,673,472 bytes,
zero swaps, revision `30e4f18dbd541c5b2f9fa90afa9c1cab92fd21ba`.
Both axiom lines are `[propext, Classical.choice, Quot.sound]`.
The first attempt's incorrect qualified sampler name is retained as a failed
receipt; its compiler-recovery axiom output is excluded from proof evidence.
Exact targets, argv, source/import hashes, dependencies and full output are
in `manifest.json` and per-attempt directories. The shared mkdir lock and
private objects are used; no shared object is overwritten.

This closes pass 4's *reference/model stage mismatch* under the reached
sampler domain. The model now accounts for the reads. It does not close
actual Rust byte, allocation or caller lowering, or the enriched two-pass
AcceptedRunJoin. No headline premise is removed.

## Stage 2: canonical C5 representation

`OraclePortCkptAbi5Codec.c5_k_bytes` identifies C5.encodeK itself with the
complete four-word LE32 byte list in emitted c0.a/c0.b/c1.a/c1.b order.
`c5_wide_halves` and `c5_e_bytes` identify C5.encodeE with all eight raw
words in c0-then-c1 order. `decoded_k_bytes` / `decoded_e_bytes` obtain the
required canonicality from success of the extracted strict reference
decoders. No raw noncanonical writer value is silently quotiented.

These close the previously missing **C5 side** of the representation
bridge. They do not state that extracted encode_k/e_byte/body_byte returns
those bytes, or identify the production reader with decode_k_spec/e_spec.
All 18 body fields and checksum still need complete source identification.

Attempt 4 exits 0: 29.148580375 seconds, peak RSS 3,117,940,736 bytes,
zero swaps, revision `ca3caa95e`. All five new theorem axiom reports are
`[propext, Classical.choice, Quot.sound]`. Attempts 1–3 are retained:
finite-list length simplification, div-by-one at four limb boundaries and
the actual List.ofFn_add/pair equivalence interface needed explicit proofs.
No failed compiler-recovery axiom output is accepted. No resource cap changed.

## Stage 3: dynamic emitted query-loop counter provenance

`OraclePortCkptAbi5Reached.successful_chain` handles arbitrary stop counters,
ordinary Rust errors, outer failures/divergence and successful owned-state
iteration. `emitted_body` identifies this body with the actual imported
`verifier.candidate.query_loop_loop.body` for any endpoint.
`reached_calls` instantiates the actual `queryWithOps` and discharges the
advance condition with `AspisR1Stage2.query_next`, rather than asking the
caller for a step/advance theorem. `tx1_next` gives exactly ten successful
calls and next=10 from start=0; `tx2_next` gives twelve and next=22 from
start=10. `chain_endpoint` identifies the final counter.

These are successful **emitted WithOps** execution results. Real callback
adoption, initial Accumulator::new fields and lazy pending.finish arithmetic
are not derived from counters or CFG paths. In particular rhs/power/weights
are not yet identified with C3's recurrence. The query callback itself is
not accepted by name as a frozen production instance.

Attempt 3 exits 0: 6.176296834 seconds, peak RSS 2,259,697,664 bytes,
zero swaps, revision `e0f05c24f`. All six new theorem audits use exactly
`[propext, Classical.choice, Quot.sound]`. Failed attempts 1–2 retain
metavariable goal ordering and machine-literal projection failures;
explicit argument construction and checked scalar projection equalities
resolve them. No cap, heartbeat or recursion setting is changed.

## Stage 4: allocation model and complete mutable interval

`OraclePortCkptAbi5Weights.overwrite_exact` replaces every element of an
arbitrary bounded interval through the **actual imported** IterMut.next/back
operations, preserving arbitrary prefix/suffix and giving the exact ending
iterator index. It requires no caller-provided next/writeback specification.
`allocated_overwrite_exact` composes S10 pass-4 `filled_exact` with that
interval theorem: success returns exactly the supplied decoded value list
and requested length; reservation failure returns Allocation before writes.
It is total over the reservation Bool and arbitrary matching-length values.

This closes mutable-loop **content composition in the std/allocation model**.
The decoded list is an input, not alleged production decoder provenance.
Actual Rust try_reserve_exact/resize outcome correspondence, read_checkpoint_weights
fallible read interleaving, Box::new and physical allocator/Drop state remain
separate. In particular no universal allocator-success assumption is added.
S10 pass-4's std composition endpoint targets the old frozen decision;
its local content theorem is reused without claiming endpoint transport.

Attempt 4 exits 0: 27.683180292 seconds, peak RSS 3,492,003,840 bytes,
zero swaps, revision `3283eb3a7`. Both new theorem axiom reports are
`[propext, Classical.choice, Quot.sound]`. Failed attempts 1–3 retain the
reserved `prefix` binder, list/explicit Slice namespace issues and empty-list
length simplification. No limit was raised and no shipped source changed.

## Stage 5: total ordered reference decision composition

`OraclePortCkptAbi5Decision.after_observation` substitutes the strict saved-ten
reader at the actual checkpoint position, with its returned state feeding
stage2. `decision_observation` proves total ordered address/answer **and**
Bool equality with `dV_frozen2` for every oracle, stored bytes, transcript
prefix and terminal message, including every rejection. Query uniqueness is
derived inside the reached branch; it is not a premise of this theorem.
This is a complete **reference/model decision** observation equality, not
an equality of frozen Rust programs or the annotated source experiment.

Attempt 3 exits 0: 11.033524542 seconds, peak RSS 3,605,757,952 bytes,
zero swaps, revision `1e0b88593`. Both axiom reports are
`[propext, Classical.choice, Quot.sound]`. Attempt 1 retained a reflexive
composition goal; attempt 2 then hit the default recursion limit while
reducing the large checkpoint/stage2 definitions. The replacement keeps
those stages locally irreducible and applies their symbolic observation
law. No maxRecDepth, maxHeartbeats or memory setting was raised. Failed
attempts and recovery output remain excluded from proof claims.

## Stage 6: focused union, caller evidence and precise remainder

`OraclePortCkptAbi5Freeze`, attempt 1, exits 0 in 31.607240083 seconds,
peak RSS 3,456,466,944 bytes, zero swaps, source revision `5c89dc959`.
Its 18 complete axiom reports cover all 17 new theorems and the reused
S10 `filled_exact`; every report is `[propext, Classical.choice, Quot.sound]`.
All six new modules have successful final receipts. The manifest retains
17 attempts (6 final successes and 11 superseded failures), maximum peak
RSS 3,605,757,952 bytes and zero swaps throughout. This is a focused union
against pinned cached objects, not a coherent full frozen release rebuild.

`tools/oracle-port-ckpt-abi5/provenance.py --check` reconciles all pinned
caller excerpts with current shipped bytes and maps all 22 selected CFG
relations to their exact S10 pass-4 kernel theorem names. It pins the new
checkpoint decision, six-read schedule, S10 allocation boundary and unchanged
pass-3 bounded Kani evidence. `provenance.json` preserves the 18 body blocks
plus checksum, individual offsets and exact producing-source requirements.
None is mislabelled a complete Rust-to-C5 field proof.

`tools/oracle-port-ckpt-abi5/audit.py` exits 0. `audit-result.json` records
this receipt/source/scope audit. It checks final source snapshots, successful
receipt equality, current direct-import hashes, all new theorem axiom lines,
all 22 CFG matches and source-pin regeneration; it rejects shipped/protected/
sibling/existing-Lean changes and committed binaries or oversized JSON.
No shipped file changed, so the conditional frozen-ELF rebuild gate is not
triggered. No host, Rust, SBF, runtime or adversarial job was run. No release
manifest replay is claimed: the concrete source join has not been built.
Historical bounded Kani/ELF evidence is reused within its original domain,
not relabelled as new verification. No local target directory was created.

**Precise remaining deliverable:** identify the actual frozen TX1 writer
and Pool TX2 reader, including source reservation/resize/Box and all
Reader/ResumeOps operations, with the byte/C5 reference. In particular:

- Complete extracted encode_k/e_byte/body_byte-to-C5 equations and production
  strict-reader adoption, including every malformed-byte Result path.
- Rust Prepared from sem/transcript/claims and the initial accumulator;
  actual query/field backend adoption and pending.finish's rhs/power/64 weights
  recurrence. The new counter proof does not establish those arithmetic fields.
- Concrete frozen source Calls/carriers and returned-state/error dependencies
  at the batch0/checkpoint/batch1 position, plus annotation's two executions.
  No aggregate source-join hypothesis is introduced as a substitute.
- The independent retained StoredCarrierBinding/P2/P2-prime account snapshot,
  proof suffix, public reconstruction and transaction-pair binding.

The former model-level absent-stage/interleaving obstruction is resolved;
the reference/model composition is now total. The source/operational gaps
above remain. CONE-AUDIT's checkpoint row is updated but stays **whole-cone
(d)**. **The checkpoint AcceptedRunJoin and deployed security target are not
yet established. Zero headline premises are removed.**

Recheck without compiling or using the host:

```
python3 -B tools/oracle-port-ckpt-abi5/audit.py
```

Each stage is committed locally with a plain message; no push or merge.
