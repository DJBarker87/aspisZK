"""Close the evidence report after the three reserved audits pass."""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rjn-20261029';D=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
summary=json.loads((E/'SUMMARY.json').read_text());audit_ids=[69597,69598,69599];audits=[];seen={};expected=[]
for a in audit_ids:
 v=json.loads((E/f'modules-{a}.json').read_text())[0];assert v['accepted'];audits.append(dict(attempt=a,**v))
 for ax in v['axioms']:
  name=re.match(r"'([^']+)'",ax)[1];seen[name]=ax
for p in sorted(D.glob('PV_RJN_*.lean')):
 if p.stem.endswith('Audit'):continue
 for name in re.findall(r'^theorem\s+(\w+)',p.read_text(),re.M):expected.append('R1Z.'+p.stem+'.'+name)
assert set(expected)<=set(seen),sorted(set(expected)-set(seen))
(E/'axioms-coverage.json').write_text(json.dumps(dict(all_new_theorems_covered=True,theorems={name:seen[name] for name in expected},audits=[dict(attempt=a['attempt'],module=a['module'],source_revision=a['source_revision'],source_sha256=a['source_sha256'],object_sha256=a['object_sha256']) for a in audits]),indent=2)+'\n')
p=E/'REPORT.md';s=p.read_text()
s=s.replace('Its explicit standalone producer Props state:', '''`PV_RJN_InstalledPublishOrder.actual` is checked against the selected
native dictionary. Its two remaining standalone Props are pure Plan facts:

- `PV_RJN_Producer_PlanLayout`: `proofBytes=57607`, `offOpenings=10055`,
  `offNodes=28359`, and the literal 16-byte MAGIC/S2 header.
- `PV_RJN_Producer_FrontLengths`: header, compact semantics and compact
  claim lengths are respectively 16, 7015 and 464.

`PV_RJN_LayoutInstalled.actual` and `.front_room` prove that these suffice
for the source layout and encoder-room facts below. No dictionary constant
law is left to the actual-family producer. The matching `.contextual`
ordering theorem is checked for the private corrected node contract too.

The lower-level standalone producer Props state:''')
s+='''
## Final status and next deliverable

| Assigned link | Status |
| --- | --- |
| PublishOrder | Proved parametrically for `runOf data plans`, with explicit literal Plan-layout and front-length producer Props. Exact original conclusion; a checked contextual successor uses the corrected node contract. |
| NodeAppend | Original link refuted under a successful, front-associated producer and actual layout, for arbitrary well-formed families. The malformed substitution is internal to its universal publication quantifier. Private range/provenance correction is explicit; its six multiproofs and publication-index source law remain open. |

No concrete successful fixture is claimed by this work. The obstruction is
universally quantified over every successful associated instance, not a
claim that the all-links conjunction has a concrete witness. The corrected
whole skeleton remains UNVERIFIED under (v). Stop reason: the original
NodeAppend link has a checked source-model counterexample; its proof cannot
be completed unchanged. The independent ordering work is complete within
the assigned parametric scope. The unused Lean budget is not a resource stop.

Next: the owner can adopt the private NodeAppend precondition correction,
then prove its actual six multiproof/slot associations and generic insertion
index law, and combine those with runjoin58's actual-family and joint-link
fixture witness. No existing link was edited or silently weakened here.

## Validation and resources

'''
s+=f"**{summary['attempts']} Lean launches: {summary['accepted']} accepted, {summary['rejected']} rejected; 0 Kani.**\n"
s+='IDs 69500–69528 and 69597–69599 were used; 69529–69596 remain unused (68).\n'
s+=f"All {len(expected)} new theorems are covered by the three reserved final audits\n(`axioms-coverage.json`); their printed axioms are subsets of propext,\nClassical.choice and Quot.sound. No sorry, axiom, admit, native_decide or\nraised heartbeat/recursion limit was added.\n\n"
s+='The audit source revision is `'+audits[0]['source_revision']+'`.\n\n'
s+='| ID | Exact audit target | Exit | Wall seconds | Peak RSS bytes | Swaps |\n| --- | --- | --- | --- | --- | --- |\n'
for a in audits:s+=f"| {a['attempt']} | {a['module']} | {a['exit']} | {a['wall_seconds']} | {a['peak_rss_bytes']} | {a['swaps']} |\n"
s+='''
Every attempt's source revision/hash, full import fingerprint, target, exit,
wall time, peak RSS, swap and original axiom output is retained in the
module/receipt JSONs. All 64 original output/time logs were hash-verified in
`original-module-logs.json`. All 15 rejected sources are retained by
hash-verified Git blob (`retained-failed-sources.json`). Failures were proof,
elaboration or syntax failures. One default-heartbeat failure was replaced
by a named dictionary projection. No memory or wall-time kill occurred.
Every resubmitted failed module had changed proof source; (u') was not needed.

Five quiet-window refusals occurred before attempt 69519. They launched no
compiler and consumed no ID. Each retry used the same ID after a full
180-second cooldown, as (m') and (t) require. Every actual launch had both
allowed:true and admission exit 0 in the same shell as the scope launch.
No void launch, cap increase or overlapping capped scope occurred. A second
local admission waiter was cancelled before any launch; 69520 was later used
normally for the node obstruction. The initial staging-prefix and verified
prerequisite-receipt guard corrections were also prelaunch own-input fixes;
see `own-input-prelaunch.json` and `cancelled-waiter-69520.json`.

'''
s+=f"Every scope used MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,\nTasksMax=64 and Lean -M7000. Maximum RSS was **{summary['peak_rss_bytes']} bytes**,\nwith **0 swaps**. The failed-source guard `tools/pv-rjn-20261029/compile.py`\nhas SHA-256 `{summary['failed_hash_guard_sha256']}`; it checks the 517 distinct\nhistorical rejected hashes resolved through git, plus all own failures.\nNo submitted source matches a previously rejected hash.\n\n"
s+='''Reuse under (h6) was read-only from the verified runjoin and held RJQ
cohorts, including object companions; no imported source/object was rebuilt
or written. Initial preflight: 3,605 project source/object pairs and 7,970
direct fingerprints matched. Final preflight: **3,622** pairs and **8,015**
fingerprints matched, with all **5,673** external objects and **5,438** IR
companions. Source authorities, selected variants, toolchain and ordered
project-before-external lookup were retained. RJQ source verification used
its recorded branch through git, without creating a non-RJN module locally.
The ten historical uncompiled exclusions are unchanged and uncredited;
every new RJN module is compiled. No own scope remains running.

No full frozen release replay ran: the original node contract is refuted
and no complete corrected skeleton witness or release result exists to
replay. No Rust build, ELF operation, extraction, installation, native fixture
replay or key operation ran. `commits.txt` lists the branch changes through
the audited code revision; the final evidence-only commit follows it.
'''
p.write_text(s)
print('All',len(expected),'new theorems covered; final report completed')
