# Merkle candidate acceptance to literal path — 2026-10-19

Four focused Lean targets now connect successful execution of the explicit-child candidate checker to the retained eight-way Merkle32 path mathematics. This is the source-cut candidate from the preceding parent-preimage packet, not an adopted production change. The original production checker still uses `array::from_fn`.

- `RawMerklePathWalk.loop_success_walk` derives exactly six successful emitted steps from successful loop execution, using symbolic fuel and the existing checked range-iterator lemmas.
- `RawMerkleAcceptedWalk.accepted_walk` derives that walk from the actual Boolean `true` result of the emitted candidate checker. It derives the advertised final root and zero final index from the same successful call.
- `RawMerkleStepWitness.step_success` derives the actual remainder and quotient calls, all eight source child-call equations, their assembled child vector, the selected running digest and successful parent call. The strengthened final owner is StepWitness v4; the narrower v2 predecessor is retained separately.
- `RawMerkleAcceptedLiteralPath.accepted_literal_path` derives six successful parent-call witnesses and a model authentication path whose positions are exactly the six public base-8 digits of the input index. For every oracle consistent with those finite parent-call witnesses, folding that path from the decoded input digest reaches the decoded advertised root. There is no separately assumed ideal accepted path.

The reused parent-preimage proof identifies each witness's grouped source input with the literal `0x18 || 8x32 child bytes` grammar. The existing Merkle32 binding theorem can therefore consume this path once the remaining oracle/log and leaf/caller premises are discharged.

**Scope still open.** Finite parent-call oracle consistency is an explicit premise. This packet does not prove that those witnesses are embedded, in order, in the complete runtime/global oracle log; nor does it establish freshness, a random-oracle law, leaf decoding/hash correspondence, or reachability from the complete verifier entrypoint. It does not prove production/candidate equivalence or adopt the candidate, and adds no CU/artifact claim. Its existential parent-call list is a functional witness, not a completed chronological instrumentation theorem.

**Axioms.** All four targets report `propext`, `Classical.choice`, `Quot.sound`, and the existing Aeneas `core.fmt.Formatter` boundary reached through the slice-to-array unwrap model. There is no `sorryAx`, but these results are **not** reported as standard-axioms-only. The Formatter model boundary remains explicit.

| Final target | Exit | Wall | Max process RSS (KiB) | Cgroup peak (bytes) | Swap |
| --- | --- | --- | --- | --- | --- |
| RawMerklePathWalk | 0 | 1.505 s | 2,612,464 | 292,831,232 | 0 |
| RawMerkleAcceptedWalk | 0 | 1.505 s | 2,599,540 | 282,157,056 | 0 |
| RawMerkleStepWitness v4 | 0 | 1.906 s | 2,617,136 | 298,557,440 | 0 |
| RawMerkleAcceptedLiteralPath, against v4 | 0 | 1.806 s | 2,604,428 | 285,351,936 | 0 |

Each final target ran with Lean 4.32.0 on the NUC, one thread, an interpreter threshold of 3200 MB, a 120-second watchdog, a 1 GiB memory-high/2 GiB memory-max cgroup and no cgroup swap, with fresh aggregate admission. Exact source revision, compiler/import/object hashes, commands and full axiom outputs are retained in each focused kit and readable receipt directory.

Development diagnostics are retained. Earlier local loop attempts exposed monadic tuple-rewrite errors; the last local attempt timed out under substantial host swap pressure. Native import-only inspection independently reproduced the insufficient 1600 MB interpreter threshold before any theorem elaboration; the physical cgroup peak was about 220 MB with no OOM events. The final threshold change did not increase the physical 2 GiB scope. Strengthening the child-call witness required one focused dependent recheck of the literal-path target; no full manifest replay was started.

Next proof work: construct the ordered parent-input/answer trace and embed it into the one global log; connect leaf hashing/strict decoding and the actual verifier caller; then close the original `from_fn` model correspondence or adopt and gate the explicit-child candidate.
