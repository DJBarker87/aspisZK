from pathlib import Path
import json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin63-20261029';p=E/'REPORT.md'
records=[v for q in E.glob('modules-*.json') for v in json.loads(q.read_text())];accepted={v['module'] for v in records if v['accepted']}
s=json.loads((E/'SUMMARY.json').read_text());old=p.read_text().split('\n## Final checked results\n')[0]
query='R1Z.PV_RunJoin_NativeQueryExact63' in accepted
fold='R1Z.PV_RunJoin_NativeFinalFold63' in accepted
text=f'''
## Final checked results

**Target not established. Rows removed: none. Endpoint premise reduction: zero.**
No full nine-link MODEL witness, native Nonempty P, full dynamic capture-world
interpreter, unconditional RUNJOIN_PUBLISH_COMPACT, or privacy endpoint was proved.
The literal generic two-existential sufficiency claim was refuted, as explained
above; this does not refute the shipped native implementation.

The unchanged original QueryAppend link is OPEN: successful-append byte
association {'IS CHECKED' if query else 'IS NOT ESTABLISHED'}, while totality for every
contextual publication remains open. QueryLoop63.loop retains the complete
native Result and finite 22-cell structure by symbolic induction. Cell proofs
produce the exact608+32+32+128+32=832 bytes, with no output length or byte
premise in QueryCellComplete63.complete. QueryParts63 keeps all six fields.
The source-world/effect boundary of the Result/value script is explicit: it is
not a native event interpreter or a claim that allocation events may be reordered.

The unchanged FinishContext link is OPEN. Checked source work includes the
stored root and inactive encoding; the claim append from primitive byte-domain
conditions (HighZero/whole-cell length, not installed as run assumptions);
the successful finish constructor frame; and exact tag30 reconstruction and
stored final-scalar association where the corresponding modules are accepted.
NativeFinalFold63 {'IS CHECKED' if fold else 'IS NOT ESTABLISHED'}.
The full c0/c1/f source-to-model opening image join remains open. CommonSample,
BackendInput and NodeAppend also remain open; the new raw lift cell/row work, if
accepted, is a local prerequisite, never full hinput credit. QueryContext,
QueryRange, FrontRoom and PublishOrder are checked at the new world-indexed
binding. Exactly three TrustItems remain, with no additions or transfers.

Validation: {s['attempts']} charged Lean attempts, {s['accepted']} accepted and
{s['rejected']} rejected; IDs {min(s['ids'])}–{max(s['ids'])}; zero Kani/Rust/SBF.
{s['refusals']} unlaunched refusals are uncharged, with full cooldown and same-ID
retry. Cumulative capped host wall time {s['host_wall_seconds']:.2f}s; maximum
RSS {s['peak_rss_bytes']} bytes; swaps {s['swaps']}. Caps stayed at MemoryHigh6G,
MemoryMax8G, MemorySwapMax0, TasksMax64, Lean-M7000; one scope at a time.
No proof limits were raised. The numeral-recursion failure in query-room
arithmetic was replaced with a generic symbolic inequality and a named small
width comparison. No unchanged failed source was resubmitted.

The three reserved audits are73497–73499. `axioms-audit.json` records exact
expected declarations and results; `verification.tsv`, original compressed
module logs and individual receipts retain target, exit, wall, RSS, swap,
source revision/SHA, dependency fingerprint and printed axioms. Audit credit
is for accepted declarations only. No complete frozen manifest or release
claim is made while witness and links remain open. The source hash guard is
recorded in SUMMARY.json; failed source hashes/revisions are retained.

Boundary checks are in boundaries.json. No ledger, implementation, protected
owner module, Produced, nine-link body, entropy trust list, observer, simulator,
or bad event was changed. No merge, push, key cleanup or funds operation ran.
Commit history from the exact entry revision is in commits.txt.

Next deliverable: construct the explicit nondegenerate dictionary/world MODEL
with nonempty Produced and all nine links; bind the native effect-world worker
interpreter and allocator metadata transitions through capture; formulate native
success on the reached caller domain and prove sufficiency there; close the
original QueryAppend totality and full FinishContext source/model image join.
'''
p.write_text(old+text)
print('report updated')
