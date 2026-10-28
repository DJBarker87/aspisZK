# Joint aggregation handoff

Status: BLOCKED before admission, upload, or Lean compilation. No new theorem
has been checked. Prepared source: lean/JHq_TX1.lean, namespace
AspisR1.JHq_TX1, commit cf8faa7208. No push.

## Exact infrastructure blocker

The existing fixture lane launcher delegates to
/home/dombarker/project-offloads/codex-cx-fixture-cache-20261027/S2W_run_host.py.
That shared runner asserts exactly:

```
{'memory.high':'6442450944','memory.max':'8589934592',
 'memory.swap.max':'0','pids.max':'64'}
```

The owner-approved scope instead requires memory.high=15032385536 and
memory.max=17179869184. It would fail this assertion before invoking Lean.
Local-lean rule 5 says: "Do NOT build or repair build/launcher/monitoring
infrastructure. If the launcher or host misbehaves, stop and report the exact
error in one paragraph; the lead fixes infrastructure." No launcher was
executed with incompatible caps; this is source inspection, not an observed
compile failure. No shared infrastructure was edited.

The fixture reservation.py also hard-codes 8 GiB, but an existing alternative,
codex-cx-sound-int2-20261025/JFz_reservation.py, supports --requested-bytes.
It does not implement the quiet-window check; any authorized future use must
also respect QUIET_WINDOW.json. No admission was requested, so there is no
allowed:true receipt and no authorization to launch was inferred.

JHq_INFRASTRUCTURE.json retains complete inspected script text and SHA256
hashes, with read-only SSH exit 0. No transport failure or retry occurred.
A broad initial read-only filename inventory was too noisy and was replaced
by a bounded Python-script inventory; neither operation launched a build.

## Before and proposed after

Before (checked predecessor):
JHn_TX1Frontier.of_byte_identity takes base, stage, JHe_SHARealization and
ByteIdentity, and concludes existence of one saved output with actual wrapper
acceptance, saved.val=JFx_NativeBytes.checkpoint.val, and length=1768.
JHn_ExactReturned.source separately proves ByteIdentity without hypotheses.
The predecessor draft JHn_TX1.accepted1_saved failed during import at -M7000
(attempt 090, exit 134, peak RSS 7272464 KiB, swap 0).

Proposed after (UNCHECKED): JHq_TX1.accepted1_saved applies exactly
JHn_TX1Frontier.of_byte_identity base stage JHn_ExactReturned.source.
Its complete conclusion is copied from the draft without alteration; only the
namespace and proof body change. The only propositional hypothesis is
[JHe_SHARealization]; base : AdapterRw.Ops and stage : VTop_Stages.Ops remain
universally quantified parameters. No ByteIdentity or byte-SHA premise is
added. The source contains #print for both applied lemmas and #print axioms
for the proposed theorem, but none has been executed in this job.

The exact source-level statements are retained in the three *.lean.txt
snapshots here. These are copied source, not fresh Lean statement output.
No quantifier, carrier, event, or conclusion change is proposed. No checked
premise-removal credit is claimed.

## Joint input still required

JHn_Joint.assembleJoint takes ByteIdentity and returns JointStatement, whose
full statement still quantifies trees, base, stage, data2 : Slice U8,
slot : S2W_ExtractionBoundary.Slot, and the explicit premise:

```
accepted2 : S2W_D189Wrappers.second (JHe_Natives.second base stage)
  CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier data2 slot () =
  ok (.Ok (JHg_World.e2.heap,()))
```

A TX1 theorem alone does not discharge that same-SDK TX2 accepted2 input.
No JHq_JointTX1 module or second compile was attempted.

## Validation and next deliverable

Budget used: 0/6 preflight Lean compiles, 0/2 large-scope compiles. Dependency
presence/hash preflight was not completed after the infrastructure stop;
no missing dependency was rebuilt. No new #print axioms result exists.
JHq_STATUS.json records the source revision and null compile metrics, rather
than inventing exit/RSS/wall/swap values for a process never started.

Next: the lead must provide an existing compatible runner for the authorized
14G/16G scope. Then complete dependency hash preflight and small statement
prints under normal caps, obtain explicit 16 GiB admission, and compile the
prepared JHq_TX1 exactly once at -M15000. Do not treat this source commit as
a successful aggregation. A memory failure must stop without rerun.

No runtime, Kani, Rust, SBF, full manifest, key, or wallet action occurred.
The deployed 100-bit target remains not established; headline ledger delta
is zero. Only new JHq_ source and the assigned evidence directory were changed.
