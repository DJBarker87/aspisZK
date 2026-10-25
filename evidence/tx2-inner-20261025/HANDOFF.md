# TX2 inner result: conditional composition, full requested closure OPEN

Branch `codex/cx-tx2-inner-20261025`. No push or merge. Only new `Tx2N_` modules and this evidence directory changed. **The requested closure without an additional gate is not established.** Stop reason: budget exhausted (80 charged Lean attempts, 0/30 Kani).

## Checked claims

`AspisR1.Tx2N_Accepted.accepted_pair_reader` extends Tx2I on the SAME D189 cuts. It applies `RowOrder_History.on_d189_cuts` to those cuts, under the unchanged writer/reader/history/P2Prime gates. It exports the actual reader return, cursor10, checkpoint/TX1-Vec byte identity, and

```
decodeAccumulator (bytesOf saved.val) = some (CheckpointBytes5Output.accumulator ra)
```

This is derived from successful concrete resume and physical section decoding, with NO writer-state equation or saved_ten premise. `Tx2N_Decode.actual` is the local source theorem; `Tx2N_Header`, `Tx2N_Reserved` and `Tx2N_DecodeHeader` derive the physical header, reserved-byte scan, scalar reads and cursor casts symbolically.

`AspisR1.Tx2N_Accepted.accepted_pair_inner` retains the predecessor's source cuts, first shape, Claims, expanded/owned executions, account observations, ordering, Required14 and reached-site conclusions. After the SAME history join, it supplies `Tx2N_Finish.Outcome` for THAT `s.pub/s.proof/s.checkpoint`, actual SDK digest and unit hash, and THAT TX1 returned Vec. Outcome contains the source reader/query/flush/back/finish calls. Its FinT continuation has no saved_ten or twelve input equation and additionally proves the typed verdict true on success.

`Tx2N_Execution.common` derives the actual reader/powers/geometry/pending/query/flush/finish calls. `Tx2N_Twelve.accepted` composes Port5Q1_Block/QueryBlock and the physical mutable flush on those returned arguments. Prepared query/rho/alpha fields, resumed canonicality and64-weight width come from the concrete reader's saved fields, not extra state assumptions. Geometry and pending calls come from the same source continuation. Actual proof wire is built into Parsed; header success derives57607-byte length.

`Tx2N_Install.inner` installs op18 reader, op6 source query with Q1 opening/geometry accessor and RowStd, op9 mutable flush and op17 the nominally transported Session A early-powers instance. `Tx2N_Execution.control` additionally installs actual pending, installed geometry and literal cursor10. Shape/finish remain Tx2I's source choices. Record restoration proves all other slots retained. The powers theorem invokes `AspisR1LoopPowers.early_powers_total_exact` directly.

The reader parent is `Port4A_NativeReader.resume` with the existing closed `CheckpointBytes4Ops` callbacks; Port5Q2 reader-helper refinements are reused and explicitly audited. This does not claim a new native helper adoption/extraction, full Result/effect transport, source-to-ELF proof or complete SDK security theorem.

## Premise audit and exact remaining gate

Review `before-statement.lean.txt`, `after-statement.lean.txt` (including the fully expanded Outcome definition), and `premise-audit.json`. No external acceptance, extraction, runtime, SDK trust, wire format, attack event or security metric was changed. Arbitrary stage dictionaries are specialized to the named source bodies; this is not equivalence to every old free dictionary. The generic Parsed quantifier becomes a Parsed with the actual proof wire and quantified semantic rows; the retained FinT input/read/decoded/transcript laws remain explicit. All unchanged non-TX2 predecessor conclusions remain.

The one residual STATE-provenance equation is physical Vec equality:

```
tx1_saved : savedVec = Tx2N_Reader.writer H stored publicBytes
  (prepared c i.data (SelectedChallengeMap.rhoOf i.rho) q)
  (OraclePortCheckpointStateC3.write
    (model i.data (SelectedChallengeMap.rhoOf i.rho) q)).accumulator
```

On the accepted pair, savedVec is THAT TX1 saved Vec; stored/publicBytes are `bytesOf f.proof.val` and `bytesOf f.pub.val`. `writer` is the physical1768-byte C5 encoder, with checksums, materialized as the actual U8 Vec carrier. No second saved-state equation is introduced.

**However, this does not meet the requested “do not add anything else” target.** The composition also needs the existing named query/geometry primitive contracts and instance equations, plus an explicit extra gate `authenticated_S1`: all22 packed folded payloads agree with one indexed recovered map, including repeated parents across the split. That gate was a premise of Port5Q1; it has NOT been derived from the actual installed batch on this pair. The name does not turn it into an adopted Session A hypothesis, cryptographic assumption, or proof. It is reported as an added implementation obligation. Arithmetic saved_ten/twelve derivations receive conditional composition credit only, not full premise-removal closure.

The broad reader claim is independently checked without that gate or the writer equation. No interface countermodel was produced or used as a stopping reason.

## Non-vacuity and success conditioning

`Tx2N_Nonvacuity.writer_equation` constructs, for every model input, a physical Vec satisfying the single writer equation, with exact1768-byte width and a successful accumulator decode of the ten-step state. `powers_success` derives successful powers returns on the named canonical domain. These establish local codec/powers consistency; they are NOT joint inhabitation of every actual accepted SDK/runtime/cryptographic/primitive hypothesis. No full installed TX2 success fixture was checked. Thus the requested complete non-vacuity audit remains incomplete alongside the missing recovery binding.

`Tx2N_Finish.accepted` uses the source's actual finish success and derived states in `FinT_Model.finish_value`; Outcome exports both original Boolean equalities and `D0TypedChecks.verify ... = true`. Rejection/effect/oracle-prefix/probability-law transport remains separate.

## Validation and frozen target

**Budget exhausted:80 charged attempts =78 Lean process invocations +2 prelaunch import-inventory failures (019 and040). Of78 compiles,27 built missing unchanged dependencies,51 compiled new-prefix files including the final audit.55 invocations passed and23 failed. Kani0/30. No more proof jobs were launched after080.**

The two prelaunch errors were worker import/dependency mistakes, corrected without infrastructure changes:019 named the then-unbuilt failed split module;040 mistook the extracted VTop_Stages namespace for a module. Exact errors are retained. Failed source snapshots, including discarded ResumeSplit and failed sorryAx diagnostics, have NO proof credit. No sorry/axiom/admit/native_decide/heartbeat/depth override occurs in final new source. Recursion-depth failures were replaced by symbolic guards/loop induction. There was no timeout or memory kill and no raised cap.

| Attempt | Target | Exit | Wall s | Peak RSS KiB | Swap | Source revision |
|---:|---|---:|---:|---:|---:|---|
| 43 | Tx2N_Reader.lean | 0 | 2.172818 | 5180688 | 0 | 0a2d3fd002 |
| 44 | Tx2N_Execution.lean | 0 | 2.544697 | 5196756 | 0 | 0a2d3fd002 |
| 46 | Tx2N_Query.lean | 0 | 2.099250 | 5168120 | 0 | 0a2d3fd002 |
| 50 | Tx2N_Decode.lean | 0 | 2.145864 | 5172932 | 0 | 0a2d3fd002 |
| 56 | Tx2N_Twelve.lean | 0 | 2.212101 | 5181944 | 0 | 0a2d3fd002 |
| 58 | Tx2N_Finish.lean | 0 | 2.434195 | 5185852 | 0 | 0a2d3fd002 |
| 59 | Tx2N_Accepted.lean | 0 | 3.283546 | 5201664 | 0 | 0a2d3fd002 |
| 60 | Tx2N_Nonvacuity.lean | 0 | 2.047748 | 5176004 | 0 | 0a2d3fd002 |
| 80 | Tx2N_Audit.lean | 0 | 1.764423 | 5154636 | 0 | 2f0301d0a0 |

Exact commands, source revisions/dirty notes, source SHA256 snapshots, direct object/sidecar fingerprints, Lean binary hash, status, wall, RSS, swap, cgroup identity/limits and full printed axiom lines are in each receipt/log. `validation-summary.json` checks all78 source snapshots, every final source against its passing snapshot AND committed audited revision, exact caps, zero swap and the final29-name axiom coverage. Every final new top theorem uses only a subset of `[propext, Classical.choice, Quot.sound]` (or none). Audit080:1.764423s,5,154,636KiB RSS, swap0, exit0; exact source revision `2f0301d0a0ead8e7370b2f45066776b0991a0bc4`.

Attempts043–051 replayed the dependent chain after op17 changed in042 and the reader cache was populated. Six downstream source+DIRECT-object fingerprints repeated; the transitive Install/environment had changed. These pairs are explicitly listed in validation-summary rather than omitted. No unchanged timed-out/killed job was retried. No package/frozen-manifest replay ran.

All actual compiles used the unchanged S2W launchers in `/home/dombarker/project-offloads/codex-cx-sound-int2-20261025`, one module per scope with `lake env lean -j1 -M7000 -DElab.async=false`, MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64. Peak reported RSS across all attempts was5,201,664KiB; all swaps0. Other workers were left untouched. Final host inspection has only init.scope; all owned jobs are terminal. No launcher/monitor/admission infrastructure was changed.

Canonical SInt2 objects were preferred. Missing reader/Q1 dependencies were built individually into that workspace; retained Q1/Q2/Port4 cache paths remain explicit in the LEAN_PATH receipts. This is focused checking on a pinned cache selection, NOT a complete coherent frozen-release rebuild. `final-object-metadata.json` contains only hash/size records; no objects/binaries are committed. The initial97-module dependency inventory is diagnostic, not a claim that all97 were rebuilt.

Section6 freeze: Lean toolchain `leanprover/lean4:v4.32.0`, exact binary hash recorded in each receipt; unchanged protocol/parameters/wire/features/native/Rust sources, extraction and tooling boundaries. `source-boundaries.json` confirms all inherited Tx2I pinned source/manifest hashes still match, and retains its stage-span checks. No shipped file or cfg(kani) harness changed, so no SBF/ELF rebuild trigger fired. Inherited pins, NOT newly reproduced:

- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

No key or account was created, destroyed, unlinked, transferred or cleaned up. No session A live worktree or candidate was modified. Only assigned new prefix modules and evidence changed. Stage commits are local and have plain messages; no push.

## Next deliverable

Install/compose the concrete batch on this SAME source pair and derive the indexed packed-recovery law on the actual proof/query/root carriers with the existing S1 trace/collision accounting. In particular prove consistency for folded parents repeated across TX1/TX2; an independent map/acceptance equality is insufficient. Remove authenticated_S1 from Outcome only after that checked join. Then consume Tx1Q's exact physical writer Vec equation (with the same prepared context and proof/public bytes) and complete the joint non-vacuity check. No scope/contract lowering is proposed.

S2 and the100-bit release target remain **not established**. The delivered accepted_pair_inner is an explicitly conditional source arithmetic composition, not the owner's requested closure with no additional gate.
