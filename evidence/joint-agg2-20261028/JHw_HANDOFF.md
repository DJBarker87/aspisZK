# Joint fixture assembly handoff — 2026-10-28

Status: **all three requested stages kernel-checked, conditional on the existing
453 tree SHA equations and the single deferred FixturePdaRuntime hypothesis.**
Branch `codex/cx-joint-agg2-20261028`; no push. Only new JHw_ modules and the
assigned evidence directory changed. No existing proved module was edited.

## Before and after

Before A: the exact retained JHv_Wrapper draft failed at import with -M7000,
exit 134, RSS 7,226,936 KiB. After A: `JHw_Wrapper.source` is checked under
the explicitly owner-approved aggregation scope. Namespace alone changed;
JHw_STATEMENT_COMPARE.json verifies that the entire draft statement and proof
are otherwise byte-identical. No premise was removed at this stage.

Before B: the checked wrapper required FixturePdaRuntime plus the three-field
JHi_SHARealization.SHARealization. After B: `JHw_TX2.byteSHA` supplies those
three equations with JHi_SHAProof.source, JHi_SHAPublic.source and
JHi_SHAChecksum.source. `accepted2_runtime` therefore needs only the runtime
law. The requested `accepted2` interface explicitly also takes
[trees : JHe_SHARealization]; that certificate is unused by TX2 (a recorded
unused-variable warning), but is required for TX1 and the final joint theorem.
No successful validation, authentication, decoder, native callback, accepted2,
byte identity, or checkpoint selection was introduced as a hypothesis.

Before C: JHn_Joint.assembleJoint consumed ByteIdentity and an accepted2 premise.
After C: JHn_ExactReturned.source supplies ByteIdentity and JHw_TX2.accepted2
supplies accepted2. JHq_TX1.accepted1_saved is independently applied to the
same `JHv_Configuration.adapter base` and `stage`. Both witnesses have exactly
the same checkpoint val; Subtype.ext proves equality of the saved vectors.
Thus one saved vector appears in both the original-world TX1 conclusion and
the corrected-world TX1 conclusion. Their heaps/posts remain distinct and
explicit. No heap equality or transfer from original-world acceptance alone
is asserted. The final theorem strengthens the corrected joint conclusion
with the original TX1 result; it does not silently replace either world.

## Exact checked final statements

The code below uses each module's existing `open` declarations, including
`JHv_Configuration` and `JHu_FixturePdaRuntime`. Full kernel printer output
for accepted2 and the final joint theorem is in the stage stdout logs.

### A — AspisR1.JHw_Wrapper.source

```lean
theorem source (base : Ops) (stage : VTop_Stages.Ops) (slot : U64)
    (runtime : FixturePdaRuntime base) (sha : JHi_SHARealization.SHARealization) :
    S2W_D189Wrappers.second (JHe_Natives.second (adapter base) stage)
      CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier
      JHb_DataRequest.value (.Ok slot) ()=ok (.Ok (JHg_World.e2.heap,()))
```

### B — AspisR1.JHw_TX2.accepted2

```lean
theorem accepted2 [trees : JHe_SHARealization]
    (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) (slot : U64)
    (runtime : FixturePdaRuntime base) :
    S2W_D189Wrappers.second (JHe_Natives.second (adapter base) stage)
      CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier
      JHb_DataRequest.value (.Ok slot) ()=ok (.Ok (JHg_World.e2.heap,()))
```

### C — AspisR1.JHw_Joint.source

```lean
theorem source [trees : JHe_SHARealization]
    (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) (slot : U64)
    (runtime : FixturePdaRuntime base) :
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first (JHe_Natives.first (adapter base) stage)
        CPH_FixtureData.copy CPH_FixtureData.allocator JHb_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧
      S2W_D189Wrappers.first (JHe_Natives.first (adapter base) stage)
        CPH_FixtureData.copy CPH_FixtureData.allocator JHg_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHk_WorldFirst.post saved,())) ∧
      saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768 ∧
      S2W_D189Wrappers.second (JHe_Natives.second (adapter base) stage)
        CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier
        JHb_DataRequest.value (.Ok slot) ()=ok (.Ok (JHg_World.e2.heap,()))
```

## Exact remaining hypotheses and trust boundaries

- `[trees : JHe_SHARealization]`: precisely 453 concrete mathematical tree
  digest equations, 157 tree0, 157 tree1, 139 tree2. These were reused as a
  certificate hypothesis, not proved by this task. The three separate byte
  digest equations are proved and no longer hypotheses.
- `runtime : JHu_FixturePdaRuntime.FixturePdaRuntime base`: the SAME original
  seven-call value law, `∀ seeds program, Call seeds program →
  base.op38 seeds program = JHs_PDA.derive seeds program`. Call enumerates
  master, checkpoint, lane, registry, registryProgramdata, entry and
  verifierProgramdata. It remains an explicit hypothesis, never an axiom or
  adopted runtime trust row. Its original ABI, valid-memory, compute-admission,
  runtime-SHA and pinned decompressor qualifications remain as documented in
  lean/JHu_FixturePdaRuntime.lean. The preflight prints its exact definition.

`base`, `stage` and `slot` remain universally quantified parameters.
The installed adapter is the existing JHv_Configuration.adapter; e2 and its
JFx_NativeBytes.checkpoint-backed saved bytes are unchanged. No quantifier,
carrier, frozen implementation or failure event was weakened. Installing
explicit source interpretations is a fixture-model specialization; it does
not establish arbitrary deployed-dictionary or native syscall refinements.
The existing NCX native P6/source-to-ELF and D188/deployed qualifications remain.
This is joint retained-fixture execution evidence, not arbitrary-adversary
soundness or a composed deployed security theorem. **The deployed 100-bit
target is not yet established.** The next security deliverable remains the
concrete tree certificate and deferred native/source-to-artifact obligations.

## Validation and resources

Verified first, before admission/upload: the full lead-owned agg16 hashes in
JHw_RUNNER_HASHES.json match d6d40da5e7cad196b15974eb96526f28073d20b2c24855303d69bc605ebcac0f,
9b325ab05e4aea7c8a2c3499ccef5de11898fdcba38cb803fc6a85111ca3f1dd and
8165ccff93f7d9b6043f55bf641c30c95c5af0f86d28b6e1b1ffef3aa5ea7ff6.
Unchanged copies run in the isolated JHw_cache-20261028 host directory, to keep
the runner's cwd/config/lakefile writes out of shared directories. No shared
runner or infrastructure file was edited. Final hashes are retained.

Recursive preflight traversed 7040 module names, matched all 152 imported
JHv_/JHu_/JHq_/JHn_/NCX_/NCV_ objects against historical receipt hashes, and
found no missing objects. No dependency rebuild was needed. Where cached
NCX/NCV sources were absent, checked-in source imports completed the graph;
JHw_SOURCE_IMPORTS.json records their source hashes and import lists.
JHw_EXPECTED_PINS.json records the historical pin provenance. Two initial
bookkeeping checks missed nested NCV_Reference/NCX_Reference paths due to our
basename filter; corrected before Lean ran. No object changed as a result.

One normal-cap preflight used S2W_lean_host.py, MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64, Lean -M7000: exit 0, wall 3.285570008 seconds,
RSS 6,422,552 KiB, swaps 0. Its retained validation axiom audit is standard.
All A/B/C admissions were allowed:true AND exit 0, requesting 17179869184
bytes. JSON plus stdout/stderr receipts were written BEFORE source/config scp.
No contention, quiet-window bypass, admission retry or transport retry occurred.
Each stage ran exactly one scope, with no repeated compile or raised cap:

```sh
systemd-run --user --scope -p MemoryHigh=14G -p MemoryMax=16G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_lean_host_agg16.py JHw_A.json
```

B/C substitute JHw_B.json / JHw_C.json. Each config calls the pinned lake
binary with `env lean -j1 -M15000 -DElab.async=false -o <target>.olean <target>.lean`.
JHw_COMMANDS.md records the complete launch sequence and exact commands.

| Target | Exit | Wall seconds | Peak RSS KiB | Swaps | Source revision |
| --- | ---: | ---: | ---: | ---: | --- |
| A: JHw_Wrapper.lean | 0 | 4.120367993 | 7367972 | 0 | `590323b031ab93aed4f6d8a6afa1ee7016861c8f` |
| B: JHw_TX2.lean | 0 | 4.325655526 | 7674524 | 0 | `9d582899576a0f28eaa52ae28d1875e50c132408` |
| C: JHw_Joint.lean | 0 | 4.783545786 | 7889604 | 0 | `c50bde8a61cd8cd05cd5221de617e5c85c3f4053` |

Each revision is accompanied by exact dirty-source SHA256 and immutable source
snapshots in its receipt. C is the final focused composition and axiom audit;
all five new theorems print only `[propext, Classical.choice, Quot.sound]`.
JHw_VALIDATION.json checks source identity, all admissions, cgroup limits,
-M15000 and every theorem's axioms. Per-stage receipts separately record
cgroup memory.peak; it is not conflated with /usr/bin/time peak RSS.

Budget: **1/6 preflight compiles, 3/3 large-scope compiles, 0/2 split replacements.**
No Lean failure, sorry, new axiom, broad recurrence unfolding, norm_num/decide,
full regression, frozen-release manifest replay, Rust/Kani/SBF/runtime gate,
wallet/key operation, push or merge. Compiled delivery objects remain pinned
in /home/dombarker/project-offloads/JHw_cache-20261028; their hashes and paths
are in JHw_FINAL_ARTIFACTS.json. The own preflight scratch object was removed; the three delivery objects are retained for composition. No copied corpus or cold dependency build.

Stage commits: preflight 590323b031; A 9d58289957; B c50bde8a61.
Stage C and this handoff are committed together in the final stage commit.
