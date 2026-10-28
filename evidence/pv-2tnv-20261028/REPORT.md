# Two-transaction privacy non-vacuity: D408 resume

**Partial result; 60/60 normal Lean attempts exhausted. No AGG16 request is
ready. The requested runtime-conditional joint bridge is NOT established.**

Worktree `/Users/dominic/ZK/.worktrees/pv-2tnv`, branch
`codex/pv-2tnv-20261028`, resume entry
`d13b5f585b4918648d13cd9bfd098a1d0507f9d5`. No merge or push.
The previous audit is preserved as `REPORT-before-D408.md`; its stronger
missing-bridge signatures remain obligations, not established theorems.

## What is now proved

The native joint fixture is **transfer-13**, not runjoin's index-zero transfer.
The public snapshot index is 13 and afterstate index 14. The existing runjoin
canonical transfer witness provably does not match this new public component:
`AspisR1.PV_2TNV_PublicEncoding.original_transfer_not_matching`.

The following new modules compile at the normal caps:

- `PV_2TNV_ByteEncoding`: exact selection of 47 digest windows, scalar/sequence
  windows and the complete 216-byte payment equality
  `JHb_DataRequest.bytes.drop 104 = JFx_DataPublic00.bytes.drop 1664`.
- `PV_2TNV_PublicEncoding` / `PublicLiterals`: an explicit M31 public projection
  from those bytes; source-selected words, index, roots and frontiers are proved,
  not supplied as hypotheses. `x handle := (mapPub nativePublic, handle)`.
- `PV_2TNV_Node01` through `Node20`: 460 isolated Poseidon-round equations and
  20 new append-node certificates. `PV_2TNV_AppendBinding.source` proves the
  full transfer-13 append root and carry binding. The existing runjoin
  output-pair certificate is imported read-only, never duplicated.
- `PV_2TNV_TransferCore`: the byte-derived public has the same input/output
  spend core as the existing fixture, while its append data remains index 13.
- `PV_2TNV_CanonicalWitness`: a constructed canonical witness, with the complete
  strengthened RspendPlus relation proved, including the change sentinel.
- `PV_2TNV_SourceBytes`: the byte carriers above are definitionally the
  `JFx_NativeBytes.publicInput` and `JHb_DataRequest.value` used by the joint
  source; the source transfer tag is also checked.
- `PV_2TNV_HeadlineFibre`: the witness inhabits the **exact** headline honest
  carrier, not just a parallel mathematical relation.
- `PV_2TNV_WorldData`: eleven literal account/public associations, including
  corrected master/forest pool and domain, historical anchor, and the lane's
  complete snapshot index/root/640-byte frontier.
- `PV_2TNV_FinalAudit.source_pair`: the final composed byte/data binding below.

Let `H := R1Z.PhaseWireLog2Bin.honest
R1Z.PrivacyR1HeadlineDeployedReal.input`, and let `x` be the definition above.
The exact checked headline-fibre theorem is:

```lean
AspisR1.PV_2TNV_HeadlineFibre.fibre
  {CommitHandle : Type} (handle : CommitHandle) :
  ∃ w : H.Instance, H.public w = (x handle).1
```

The exact final checked composition, with the source namespace opens, is:

```lean
AspisR1.PV_2TNV_FinalAudit.source_pair
  {CommitHandle : Type} (handle : CommitHandle) :
  ∃ w : H.Instance,
    H.public w = (x handle).1 ∧
    JHb_DataRequest.value.val.drop 104 =
      JFx_NativeBytes.publicInput.val.drop 1664 ∧
    (JHb_DataLane.value.val.drop 128).take 640 =
      (JFx_NativeBytes.publicInput.val.drop 336).take 640
```

These are lower mathematical/byte-binding helpers. **They are not the requested
end-to-end non-vacuity theorem.** They do not assert wrapper execution, native
prover generation from this witness, a native commitment handle, or experiment
refinement. A handle remains a parameter. The projection's field equations are
checked; an equality to the extracted decoder's projected native record has
not been elaborated here.

## Carrier audit and exact missing bridge

The locally preserved joint conclusion remains byte-for-byte in
`JOINT-CONCLUSION.lean.txt`; its source is `JHx_Joint.source.lean.txt`.
No new checked declaration restating that complete Prop and consuming its
proof `p` was delivered. In particular, no theorem was compiled that combines
`p` with the new fibre and identifies the actual original/corrected TX1 and
TX2 wrapper expressions with that public/witness pair.

The remaining normal-cap deliverable must:

1. Restate the exact joint conclusion locally, without importing its closure.
2. Prove the native decoder/public projection and actual statement-handle
   association, using the new source byte and canonical-witness helpers.
3. Prove that the exact `JHb_World.e1` / `JHg_World.e1` / `JHg_World.e2`
   wrapper inputs in `p` carry that public data, on the same installed SDK
   and saved bytes. Keep the two heaps distinct.
4. State the resulting implication with explicit named binders
   `(runtime : AspisR1.JHu_FixturePdaRuntime.FixturePdaRuntime base)` and
   `(p : J base stage slot)`; neither may be assumed discharged.

**FixturePdaRuntime base remains NOT discharged, NOT adopted for privacy, and
NOT added to T.** The new helper results need no runtime law because they assert
only mathematics and literal data. No requested wrapper/non-vacuity theorem
omitting the required runtime binder is claimed.

For the experiment carrier, read-only runjoin source identifies the template

```lean
R1Z.PV_RunJoin_Deployed.rust runtime
```

whose `Adversary` is definitionally `R1Z.GamesR1.R1Adv K CommitHandle Aux`.
Runjoin's existing `PV_RunJoin_Source.idleObserver` inhabits that carrier.
However, neither the joint conclusion nor this work constructs a **native
associated** `PV_RunJoin_Deployed.Runtime` (world, account, body, disclosed view,
observer oracle and ideal interpreter). Thus no actual deployed instance or
inhabitant at such an identified instance is newly established here.

The definition of the template does not itself require refinement. Once a
native runtime instance is identified, the remaining security bridge belongs
to runjoin and is exactly

```lean
R1Z.PrivacyR1HeadlineDeployedReal.RustRealRefinement
  template outputs x (R1Z.PV_RunJoin_Deployed.rust runtime)
  (R1Z.PV_RunJoin_Deployed.observer_program runtime)
```

with the unchanged quantification over every adversary and matching witness,
exact RunJoin marginals, old-bad event and seed-query function. This job neither
proves it nor replaces it with honest acceptance. No implication that instance
construction logically requires RustRealRefinement is asserted: native runtime
identification and that refinement are distinct remaining obligations.

## Per-suspect disposition

| Suspect | Newly checked | Still retained |
| --- | --- | --- |
| V045 | An explicit byte-derived public component and complete mathematical witness, with native-byte aliases and account data associations. | No identified deployed runtime/FSExperiments instance; no native handle or exact joint-wrapper association. Runjoin's unchanged RustRealRefinement remains the security refinement obligation. |
| V046 | No new deployed-carrier inhabitance theorem. The existing runjoin R1Adv inhabitant is reusable once its runtime instance is identified. | Arbitrary rust.Adversary may be empty; the actual deployed instance is not identified here. |
| V047 | A constructed matching witness at the exact headline H for every supplied handle on the explicit transfer-13 byte-derived public; the old index-zero witness is checked not to match. | Arbitrary-x non-vacuity, native handle/decoder association and the exact same-wrapper execution implication from J remain unproved. |

No privacy endpoint premise was removed, added or changed. T is still exactly
entropy_law, entropy_kernel, observation. No simulator, observer, headline
quantifier, release program or soundness proof was edited. Target not yet
established.

## Validation and AGENTS.md section 6 receipts

`resume/VALIDATION.json` contains all 60 launch receipts, including exact target,
command, source revision and SHA256, dependency fingerprint, admission result,
exit, wall time, peak RSS, swap and complete printed axioms. Raw outputs and GNU
time logs are retained separately. Source_revision is launch HEAD; the separate
source SHA256 pins each working candidate, including candidates not yet committed
at launch. All final accepted source hashes were checked against the delivered
files. These are focused cached proofs, not a new frozen-release replay.

| Field | Final composed audit |
| --- | --- |
| Target | `PV_2TNV_FinalAudit`, env-J ID 60997 |
| Exit status | 0 |
| Wall time | 2.104732499923557 seconds |
| Peak RSS | 4,480,248 KiB |
| Swap | 0 |
| Source revision | `2ca48c204d` (full revision and exact source hash in receipt-60997.json) |
| #print axioms | source_pair and audited roots: only propext, Classical.choice, Quot.sound |

Budget: **60/60 normal Lean processes; 57 pass, 3 rejected; 0 Kani; 0 AGG16**.
IDs 60900–60958 and 60997 only. Summed recorded attempt wall time
612.9604972936213 seconds; maximum RSS 4,521,520 KiB; swaps zero throughout.
Every scope used MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64,
Lean -M7000. Only one scope at a time.

Rejected attempts and changed replacements:

- 60900: import failed on a dangling Aeneas link in the shared env-J prefix.
  60901 selected the existing read-only runjoin library prefix, after h4 checks;
  no shared infrastructure was repaired or changed.
- 60922: missing Nat.zero_add rewrite in the generic digest-window proof.
  Changed proof passed as 60923.
- 60957: recursion depth while reducing the 640-byte frontier equality.
  The generator now emits a named symbolic chunks lemma and twenty bounded
  32-byte comparisons. Changed proof passed as 60958; no limit was raised.

The initial 60900 reservation refusal started no compiler and consumed no ID;
its same-ID retry occurred after the required cooldown. Its first refusal log
was overwritten by the successful admission log; the exact refusal is retained
in `resume/INITIAL-REFUSAL.json` and the conversation tool receipt. No refusal
is counted as a Lean attempt. No transport retry, memory kill or timeout occurred.

The full source pin graph is `resume/source-closure.json`. The read-only model
closure is `resume/model-resolution.json` / `model-cache-check.json`: 771 project
objects, plus all 5673 external objects under h4, checked before the relevant
imports. The known EJR workspace alternatives are resolved to the byte-exact
record used by the runjoin endpoint cohort and checked with its entire import
fingerprint; no differently hashed dependency was substituted. Historical
missing source paths use exact pinned passing receipt snapshots. No joint
SHA453/fixture cache or ad-hoc Stream A P6 bridge object was imported; the
literal native carriers were rebuilt privately. The inherited env-J search
path retains historical frozen union prefixes; every selected baseline object
is accounted for by the external authority or the checked runjoin cohort.
No runjoin module was edited or duplicated.

Generators --check passed for byte windows, bounded append certificates, field
literals and world-data windows. No large recurrence, norm_num or decide gate
was used; finite round equations and small bit/index bounds are explicit.
No local Lean, Rust, Kani, extraction or SBF build ran. Artifact pins remain
inherited; no fresh artifact fidelity or release result is claimed.

## Stop and next deliverable

Stop reason: **normal Lean budget exhausted**, not mathematical impossibility
and not completion of the requested scope. The exact conditional joint bridge,
required runtime binders and native decoder/handle/execution associations are
still missing. No single consumer whose only remaining input is JHx_Joint.source
is ready, so neither a consumer nor AGG16-REQUEST.json was staged. No AGG16 scope
was launched. The next deliverable is the normal-cap implication described above,
reusing these compiled transfer-13 helpers; RustRealRefinement stays with runjoin.
