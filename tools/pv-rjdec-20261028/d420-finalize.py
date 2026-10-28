"""Freeze only measured receipts; leave native obligations explicitly open."""
from pathlib import Path
import json,subprocess,re,datetime
E=Path('evidence/pv-rjdec-20261028');x=json.load(open(E/'d420-validation.json'));assert x['attempts']==100 and x['accepted']==99 and x['rejected']==1 and not x['unused_IDs']
receipts=[json.load(open(E/f'receipt-{a}.json')) for a in range(61800,61900)]
for r in receipts:
 assert r['launch_admission']['allowed'] is True and r['reservation']['allowed'] is True
 assert r['swaps']==0
for p in E.glob('modules-618*.json'):
 for v in json.load(open(p)):
  if not v['accepted']:continue
  for s in v['axioms']:
   q=re.search(r'depends on axioms: \[([^\]]*)\]',s,re.S)
   if q:assert set(z.strip() for z in q[1].split(',')) <= {'propext','Classical.choice','Quot.sound'},(v['module'],s)
intervals=[]
for r in receipts:
 t=json.load(open(E/f"transport-{r['attempt']}.json"));start=datetime.datetime.fromisoformat(r['utc']).timestamp();intervals.append(dict(attempt=r['attempt'],start_epoch=start,end_epoch=start+t['wall']))
for a,b in zip(intervals,intervals[1:]):assert a['end_epoch']<=b['start_epoch'],(a,b)
(E/'d420-scope-sequence.json').write_text(json.dumps(intervals,indent=2)+'\n')
plan=json.load(open(E/'build-plan.json'));accepted={v['module'] for p in E.glob('modules-618*.json') for v in json.load(open(p)) if v['accepted']}
order=json.load(open(E/'d420-followup-order.json'))['order'];uncompiled=[m for m in order if m not in accepted]
assert uncompiled==['R1Z.PV_RunJoin_CausalHeadline'],uncompiled
(E/'d420-uncompiled-sources.json').write_text(json.dumps({'staged_not_compiled':uncompiled,'credit':False,'final_audits_import_them':False},indent=2)+'\n')
report=E/'REPORT.md';s=report.read_text();s=s[:s.index('Validation and final budget accounting are pending')]
s+='''**Fresh budget exhausted: 100 Lean attempts, 99 accepted / 1 rejected;
0 native scopes; 0 Kani; 0 VOID attempts.** Every ID 61800–61899 launched
exactly one compiler. The three reserved audits passed. The 61842 reservation
refusal launched no compiler; its same-ID retry followed the full cooldown.
Every admitted launch checked exit zero and `allowed:true` in the same shell
command as the scope. MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64,
Lean -M7000 throughout. No cap or prover limit was raised.

| ID | Exact target | Exit | Scope wall s | Peak RSS bytes | Swap |
| --- | --- | --- | --- | --- | --- |
'''
for a in [61897,61898,61899]:
 r=json.load(open(E/f'receipt-{a}.json'));assert r['accepted'];s+=f"| {a} | `{r['modules'][0]}` | {r['exit']} | {r['host_wall_seconds']} | {r['peak_rss_bytes']} | {r['swaps']} |\n"
s+='\nAudit source revisions: '+', '.join(f"{a}: `{json.load(open(E/f'receipt-{a}.json'))['source_revision']}`" for a in [61897,61898,61899])+'. No Lean source changed afterward.\n'
s+=f'''
All accepted printed axiom sets are subsets of propext, Classical.choice and
Quot.sound. Peak RSS over the fresh budget was **{x['peak_RSS_bytes']} bytes**;
all swaps were zero. Complete exact source pins, targets, dependency
fingerprints, commands, admission records, exits, wall times, RSS, swap and
axiom lines are retained in `receipt-618*.json`, `modules-618*.json` and the
original per-module output/time files. `d420-original-logs.json` hashes those
original files. `d420-own-validation.json` checks all accepted private sources,
objects and import fingerprints, including the retained predecessor objects.

Attempt 61866 was rejected at default simplifier recursion depth while
expanding the emitted afterstate decoder. It is not credited. The generator
now uses `ParserR15.source_chunk` and its already checked named `reference`;
that changed source passed as 61867, with unchanged limits. The failed Git
blob and original diagnostics are retained in `d420-failed-sources.json` and
`61866-00.out`. The other three generated prefix modules remain byte-identical;
the generator's `--check` passed. No unchanged failed source was rerun.

The missing constructor/caller objects were rebuilt privately, unchanged,
solely to check the observation forwarding and retained headline signatures.
No new helper-effect association for item (b) is claimed. The final generic
`PV_RunJoin_CausalHeadline` source remains staged but uncompiled after the
charged rejection consumed its slot; it is excluded from both final audits
and proof credit. The installed and joined headline signatures are audited.
This is a focused cached replay, **not** a frozen-manifest release replay,
new artifact-fidelity result or native implementation proof.

The initial inherited-cache preflight verified 2,764 project source/object
pairs, 5,802 import fingerprints, 5,673 external objects and 5,438 IR companions.
The final read-only preflight rechecks those pins. `d420-scope-sequence.json`
records disjoint launch intervals. `d420-local-input-corrections.json` records
compile-free staging/audit corrections. The exact commit list since entry is
`d420-commits.txt`; the final evidence-freeze commit follows its generation.
No other worktree, shared source/object, shipped source, wallet or account key
was edited; no extraction, Rust/native gate, ELF rebuild, push or merge ran.

## Next concrete deliverable

Construct and identify the two actual native observation adapters, including
their installed call sites. Prove both reachable full failure/divergence-prefix
fibres and the six fixed-decoder total Result clauses before supplying Common.
Then identify the actual native public record and commitment handle, prove
`actual = PV_2TNV_PublicEncoding.x native_handle`, and use the checked
`PV_RJDec_V047Native.consume`. Keep FixturePdaRuntime and joint wrapper proof
binders explicit wherever those wrapper implications enter. Items (a) and (c)
remain OPEN; item (b) remains with pv-own. Endpoint and whole-row removal: zero.
'''
report.write_text(s)
(E/'d420-commits.txt').write_text(subprocess.check_output(['git','log','--oneline','11d5d0368b..HEAD'],text=True))
print('Frozen fresh budget:',x['attempts'],'attempts;',x['accepted'],'accepted;',x['rejected'],'rejected')
