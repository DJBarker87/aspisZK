from pathlib import Path
import json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin43-20261028'
t=json.loads((E/'final-tally.json').read_text());assert t['attempts']==100 and t['attempt_ids']==list(range(60400,60500))
f=json.loads((E/'fresh-preflight.json').read_text());assert f['all_match']
audits=[json.loads((E/f'receipt-{a}.json').read_text()) for a in [60497,60498,60499]];assert all(x['accepted'] for x in audits)
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
table='\n'.join(f"| {a['attempt']} | {a['modules'][0]} | {a['exit']} | {a['host_wall_seconds']} | {a['peak_rss_bytes']} | {a['swaps']} |" for a in audits)
text=f'''# Runjoin43 — actual caller domain and opening source construction

Worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch
`codex/pv-runjoin-20261026`. Entry `cbec9b692502c78e2d4914724f3c51c2408838e3`,
resume LOG D401. Final source/evidence preparation revision `{head}`.
Assigned IDs **60400–60499**, audit IDs **60497–60499**.

**Target not yet established. Whole ledger rows removed: 0.**
Stopped on the **100-attempt Lean budget**, with **0 Kani**.
Exactly **{t['accepted']} accepted / {t['rejected']} rejected candidates**; all three reserved audits passed.

## Completed step (1): actual caller Domain

`R1Z.PV_RunJoin_CallerDomain43.post` (60430) and
`CallerSuccess43.success` (60432) prove that every successful actual emitted
`host_semantic.build_with_helper_mode` output has exactly 13831 bytes and satisfies
`SemanticDomain40.Domain` at count 27, initial cursor 32 and row 0. The theorem
quantifies over the actual helper and commitment implementations and input arrays.
No successful encoder/loop, desired byte equality, semantic-oracle meaning, or
op227 law is a premise.

The proof threads the initial root, empty records, C2 root, actual 50-byte
zero-claim accumulation, mask word, ten actual 896-byte canonical round records,
3712-byte claim record, 928-byte endpoint record and both circle-record continuations.
`LayoutPieces43.domain` discharges all thirteen canonical payload offsets through
the fixed layout constructor. **Every one of the 27 entries** in
`caller-domain-obligations.json` now has a checked whole-caller association.

RecordPost43, ByteExtension43, CanonicalRecord43 and RecordSlice43 preserve
framing, lengths, payload slices and prefixes. ZeroRows43/ZeroComplete43 and
RoundRecord43/RoundAccum43/RoundComplete43 supply the actual loop laws.
The actual source Results retain their failure, divergence and inner-error branches.
This byte-domain result does not establish witness-independent failure observations
or native/deployed correspondence.

## Step (2): verified progress and retained gap

All **39** staged opening-model modules were source-hash verified and compiled once
in topological order, IDs 60433–60471, reusing the previously verified objects.
This includes `ProverCommitOpeningModel53.exact_result` and
`ProverCommitOpeningFolded54.exact_result`. The order and absence of pre-existing
objects are recorded in `opening-prerequisite-order.json` and
`opening-prerequisite-preflight.json`. No unchanged object was rebuilt.

WordLimb43 and WidePoint43 establish symbolic byte/limb/product-index laws.
WideImage43 proves the current canonical wide encoder's exact retained byte image;
EncodedImage43 proves the complete actual encoded_slice Result's ordered image.
`FoldedEncoding43.encode` composes the retained complete opening producer with
that current encoder for its derived four-value folded leaf. It does **not** identify
the current PreparedOpening constructor with the retained producer. That association
remains open and was not added as an endpoint premise.

OpeningWord43.value identifies both Base and Secure actual stored-word reads,
including raw field normalization and index errors. OpeningLane43.complete proves
all four actual values in order. FibreFillThread43 retains each of the four mutable
array backward/restoration continuations and proves the finite ordered fill.
`FibreOpening43.complete` identifies the actual constructor with this stored-word
fill and the exact path-slot update on its explicit at-most-29-lanes domain.
These complete-Result source associations do not establish native helper effects,
Merkle authentication, or the complete query/node security-model byte equation.

**Step (2) remains incomplete:** the current PreparedOpening association, complete
22-query opening construction, six actual node multiproofs and publication indices,
and publish_compact's complete ordered proof bytes remain open. Steps (3) and (4)
were not started, respecting the requested order. Both native ROMView decoder laws
supplied to CommonSample32/CommonObserver32, installed native helper effects,
the security-model proof-byte equation and RustRealRefinement remain open.

## Unchanged endpoint and trust boundaries

No endpoint field or whole ledger row is removed, added, weakened or changed.
V038, V045, V163, V165, V167 and V244 remain. The eight PV_RunJoin_Premises fields
remain exactly source_V045, E1_V329, native_fill_V336, native_ledger_V337,
byte_blind_V338, kernels_V339, disclosed_V038 and observerOracle_V038.
Before/after source statements are byte-identical in
`endpoint-boundaries-unchanged.json`: removed/added/weakened/changed = 0/0/0/0.
TrustItems remains entropy_law, entropy_kernel, observation.

The observer, simulator, coupling, bad/query events, public guards, failure/divergence
observations and side-channel obligations are unchanged. OracleBridge38's op227
selected-callback bridge remains unchanged with its single named hypothesis and is
not used in any credited endpoint result. **Op227 is not the sole refinement gap.**

## Validation and process

The initial read-only preflight checked 2633 project source/object pairs, 5519 import
fingerprints, 5673 external objects and 5438 IR companions. The final preflight checks
**{len(f['projects'])} project pairs**, **{len(f['dependencies'])} import fingerprints**,
**{len(f['external'])} external objects** and **{len(f['ir'])} IR companions**, all matching.
The pinned private runjoin32-lean workspace/cache is retained.

Each launch used one module in one scope, MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64, Lean -M7000. Every launch required allowed:true
and admission exit 0. Reservation refusals and the transient cgroup-scan race were
uncharged; full cooldowns and the same unlaunched IDs were retained. No cap was
raised. There was no memory kill or external timeout. The scope sequence is disjoint.

Rejected 60472/60474 concrete byte-image reductions hit the default heartbeat limit.
Their replacement uses symbolic limb and product-index lemmas, then the fast joined
image (60480). Later inference/phase heartbeat failures were replaced by explicit
function/dictionary/phase associations, without changing resource settings.
`retained-failed-sources.json` verifies every rejected source's retained Git blob.
The lane model's getter was made explicitly identical to the installed source
getter; earlier implicit-binding candidates are rejected, not proof credit.

The first source-audit staging request rejected uncompiled unchanged endpoint/trust
imports before a compiler or ID was consumed. The focused audit was corrected to
its verified private closure. `audit-staging-input-correction.json` records this.
Endpoint/trust before-and-after statements are checked by source identity, not a
new endpoint-closure replay.

| ID | Focused audit | Exit | Scope wall s | Peak RSS bytes | Swap |
| --- | --- | --- | --- | --- | --- |
{table}

All accepted printed axiom sets are subsets of propext, Classical.choice, Quot.sound.
Every original module output/time pair is hash-verified in
`original-module-logs.json.xz`. `receipt-*.json` and `modules-*.json` record targets,
commands, exact source revisions/blobs/hashes, import fingerprints, exit statuses,
wall time, RSS, swap and printed axioms. Overall peak RSS is **{t['peak_rss_bytes']} bytes**;
all swaps are zero. `toolchain-and-final-scopes.json` records Lean 4.32.0, pinned
commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, and no own running scopes.
These are focused source/model audits, not a final frozen-manifest release replay.

`stage-A-source-identity.json` verifies the empty crates/, programs/ and
 tools/r1-cost-probe diff from 82566acdfb. Historical stage-A evidence is reused
only in that unchanged-source scope. No shipped source, key/account, other worktree,
shared source/cache or release artifact was changed. No push, merge, extraction,
Kani/native differential, ELF rebuild or unchanged full regression was performed.
Compiler-cohort, deployed feature/profile/ABI, D188, allocation/TLS/filesystem,
Drop/unwind, failure-independence, K-1/K-2 and side-channel qualifications retain
their prior scope; no new native credit is claimed.

## Next concrete deliverable

Associate the current PreparedOpening constructor with the retained complete
opening producer, then prove the actual append_query_openings and append_node_slots
byte lists from the stored commitments/folded data and thread them through
publish_compact. Only after step (2) is complete should the native decoder/effect
installation and security-model/RustRealRefinement composition proceed.

`commits.txt` lists all commits since entry; the final evidence-freeze commit follows
its generation. The private verified cache remains available for dependent work.
'''
(E/'REPORT.md').write_text(text)
print('Wrote complete round report')
