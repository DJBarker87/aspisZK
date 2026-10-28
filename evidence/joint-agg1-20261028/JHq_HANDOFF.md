# TX1 aggregation handoff — 2026-10-28

Status: **CHECKED, conditional only on JHe_SHARealization.**
`AspisR1.JHq_TX1.accepted1_saved` in `lean/JHq_TX1.lean` applies exactly
`JHn_TX1Frontier.of_byte_identity base stage JHn_ExactReturned.source`.
No existing proved module or shared infrastructure was edited. No push.

## Before and after

Before: the checked `JHn_TX1Frontier.of_byte_identity` required
`identify : JHn_TX1Frontier.ByteIdentity`, in addition to
`[trees : JHe_SHARealization]`, with universally quantified `base` and `stage`.
The independently checked `JHn_ExactReturned.source` proves that byte identity
unconditionally. Their final application was previously unchecked: predecessor
attempt JHn35_090 failed during import at -M7000, exit 134, peak RSS
7,272,464 KiB, swap 0. The earlier worker stopped before compilation because
the shared runner asserted 6G/8G; that historical inspection remains in
JHq_INFRASTRUCTURE.json.

After: the final application is kernel-checked. The complete statement is:

```lean
variable [trees : JHe_SHARealization]
theorem accepted1_saved (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first (JHe_Natives.first base stage)
        CPH_FixtureData.copy CPH_FixtureData.allocator JHb_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧
      saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768
```

JHq_STATEMENT_COMPARE.json confirms that the statement text following the
name is byte-identical to the predecessor draft's accepted1_saved statement.
No carrier, heap, quantifier, event, or conclusion changed. The existing
ByteIdentity interface premise was discharged; no premise was added.
In particular no byte-SHA, acceptance, writer identity, or TX2 premise is
required by this theorem. `base : AdapterRw.Ops` and `stage : VTop_Stages.Ops`
remain universal parameters.

The sole retained propositional assumption, JHe_SHARealization, comprises
453 concrete SHA tree equations: 157 for tree0, 157 for tree1, and 139 for
tree2. This job did not prove those equations. The theorem is an actual
retained-fixture TX1 wrapper acceptance/byte identity result, not a deployed
security theorem or an arbitrary-adversary soundness result.

## Verified launchers and preflight

Lead-owned SHA256 values were verified first, before admission or uploads:

| File | SHA256 |
| --- | --- |
| reservation_agg16.py | d6d40da5e7cad196b15974eb96526f28073d20b2c24855303d69bc605ebcac0f |
| S2W_lean_host_agg16.py | 9b325ab05e4aea7c8a2c3499ccef5de11898fdcba38cb803fc6a85111ca3f1dd |
| S2W_run_host_agg16.py | 8165ccff93f7d9b6043f55bf641c30c95c5af0f86d28b6e1b1ffef3aa5ea7ff6 |

JHq_RUNNER_HASHES.json records the initial verification. The recursive
JHq_CLOSURE_PREFLIGHT.json matched all 95 JHn_/JHe_ objects (73/22) selected
by the inherited joint-fixture35 LEAN_PATH against historical manifests or
consumer receipts. No missing dependency was found or rebuilt. None of the
285 checked .olean.server/.olean.private/.ir companions was present
(JHq_COMPANIONS.json). Objects and compiled dependency evidence were reused;
there was no cold build, package replay, or full manifest regression.

Three separate normal-cap preflights used unchanged S2W_lean_host.py with
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -M7000:

| Target | Exit | Wall seconds | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| JHq_PreflightFrontier | 0 | 3.290675 | 7127820 | 0 |
| JHq_PreflightIdentity | 0 | 3.109145 | 6745112 | 0 |
| JHq_PreflightJoint | 0 | 3.336260 | 7128100 | 0 |

Their stdout logs print the exact frontier and identity lemmas, the SHA
realization class, and the expanded joint statement. JHq_RESULTS.json and
each attempt's receipt retain exact commands, source revisions, timings,
limits, and statement/axioms output. The print-only modules introduce no
new theorem, so their axioms lists are empty.

## Single approved aggregation attempt

The first reservation_agg16.py request admitted: allowed=true AND exit 0,
requested_bytes=17179869184, bounded_reserved_bytes=17179869184; projected
reservation 32 GiB <= 55 GiB. Host stdout/stderr and JSON were saved before
any upload. No contention, quiet-window bypass, transport retry, or repeated
compile occurred.

Exact launch (from the shared fixture-cache directory):

```sh
systemd-run --user --scope -p MemoryHigh=14G -p MemoryMax=16G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_lean_host_agg16.py JHq_agg16_tx1.json
```

The configured command was:

```sh
/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake env lean -j1 -M15000 -DElab.async=false -o JHq_TX1.olean JHq_TX1.lean
```

Target: AspisR1.JHq_TX1.accepted1_saved.
Source revision: d2465903547e0c87714c3af2c79607de4215cad5 (clean source tree
at configuration). Source SHA256:
87425e2f50dd3b9cd2dc01ef74a3ee2584ba4f0b9c49b213373795a71f635ba3.
Exit 0; wall 4.118656793027185 s; peak RSS 7,528,024 KiB; swaps 0.
The runner separately records cgroup memory.peak=823947264 bytes and verifies
memory.high=15032385536, memory.max=17179869184,
memory.swap.max=0, pids.max=64. These are distinct recorded metrics.

The complete audit output is:

```text
'AspisR1.JHq_TX1.accepted1_saved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Primary evidence: JHq_agg16_tx1/receipt.json, stdout.log, time.log, and its
sources/JHq_TX1.lean snapshot; JHq_agg16_tx1-admission.json,
JHq_agg16_tx1-barrier-0.log, and JHq_agg16_tx1-command.txt.
The compiled object is retained in the pinned fixture lane, not copied
locally; JHq_FINAL_ARTIFACTS.json records its path/hash and final runner hashes.

## Exact remaining joint input

The normal-cap print confirms that assembleJoint takes ByteIdentity and
returns JointStatement, whose expansion explicitly retains, for the SAME
base/stage SDK and corrected joint world, data2 : Slice U8,
slot : S2W_ExtractionBoundary.Slot, and:

```lean
accepted2 : S2W_D189Wrappers.second (JHe_Natives.second base stage)
  CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier data2 slot () =
  ok (.Ok (JHg_World.e2.heap,()))
```

That accepted2 input is not provided by the new TX1 theorem. Also,
assembleJoint consumes ByteIdentity, not an accepted1_saved proof, and
its TX1 conjunct uses JHg_World.e1/JHk_WorldFirst.post rather than the
retained target's JHb_World.e1/JHe_WrapperReady.post. Therefore no
JHq_JointTX1 module or second large compile was attempted under the task's
TX2-input alternative. The existing conditional joint assembly is not
claimed as a closed same-SDK joint execution.

Next deliverable: supply the native same-SDK TX2 witness with precisely the
accepted2 type above, retaining the D188/native/source-to-ELF qualifications;
then compose using the corrected TX1 interface and the proved byte identity.
JHe_SHARealization remains open. The deployed 100-bit target is not yet
established; no headline security credit is claimed.

Budget used: 3/6 preflight Lean compiles, 1/2 large-scope compiles. No new
recurrence, generic proof, Rust/Kani/SBF/runtime gate, wallet, key, or shared
infrastructure modification occurred. Changes are confined to JHq_ modules and
this evidence directory. Stage commits: a88963e3f6 (runners/preparation),
d246590354 (preflight); the final evidence commit follows this handoff.

The launcher's display excerpt had a whitespace-only truncated line; it was
trimmed for the evidence diff. JHq_EXCERPT_FORMATTING.json records both hashes.
The complete stdout.log/time.log/receipt.json bytes are untouched.
