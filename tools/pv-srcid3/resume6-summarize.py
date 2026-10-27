#!/usr/bin/env python3
import pathlib,json,re,hashlib,subprocess
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026';a=[json.loads(x) for x in (e/'resume6-attempts.jsonl').read_text().splitlines()];rejected={r['attempt'] for r in json.loads((e/'resume6-rejected-profiles.json').read_text())}
lines=['# Resumed Lean receipts, allocation 6','','Caps: Lean -M7000, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; one capped scope at a time. All raw output, timings, exact source/input hashes and complete printed axioms/errors remain in resume6-attempts.jsonl and out/time/sha-ID files. Kernel success is distinct from the standard-axiom/profile validation.','','| ID | Exact target | Kernel exit | Validation | Wall | Peak RSS KiB | Swap | Source revision | Axiom reports |','| --- | --- | --- | --- | --- | --- | --- | --- | --- |']
for r in a:
 valid=r['exit']==0 and not r['nonstandard_axioms'] and r['axiom_reports_complete'] and r['attempt'] not in rejected
 status='standard' if valid else 'REJECTED '+(','.join(r['nonstandard_axioms']) or ('profile' if r['attempt'] in rejected else 'compile/report'))
 lines.append(f"| {r['attempt']} | {r['module']} | {r['exit']} | {status} | {r['wall']} | {r['peak_rss_kib']} | {r['swaps']} | {r['source_revision'][:10]} | {len(r['axioms'])}/{r['expected_axiom_reports']} |")
(e/'RESUME6-RECEIPTS.md').write_text('\n'.join(lines)+'\n')
files=[]
for p in sorted((root/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_Src_*.lean')):
 if p.stem.startswith('PV_Src_FinalAudit6'):continue
 if subprocess.run(['git','cat-file','-e','92d3db0b2f:'+str(p.relative_to(root))],capture_output=True).returncode==0:continue
 sha=hashlib.sha256(p.read_bytes()).hexdigest();matches=[r for r in a if r['module']=='R1Z/'+p.stem and r['source_sha256']==sha and r['exit']==0 and not r['nonstandard_axioms'] and r['axiom_reports_complete'] and r['attempt'] not in rejected]
 s=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S);s=re.sub(r'--[^\n]*','',s);bad=re.findall(r'\b(?:sorry|admit|native_decide|implemented_by|axiom)\b',s)
 files.append(dict(path=str(p.relative_to(root)),sha256=sha,accepted_attempts=[r['attempt'] for r in matches],forbidden=bad))
(e/'resume6-new-source-audit.json').write_text(json.dumps(files,indent=2)+'\n')
used=int((e/'resume6-next-id.txt').read_text())-37100
budget=dict(authorized_lean=100,charged_lean=len(a),remaining_lean=100-len(a),authorized_kani=4,charged_kani=len((e/'resume6-kani-invocations.jsonl').read_text().splitlines()),allocated_IDs=list(range(37100,37100+used)),next_unused_ID=37100+used,unaccepted_attempts=[r['attempt'] for r in a if r['exit'] or r['nonstandard_axioms'] or not r['axiom_reports_complete'] or r['attempt'] in rejected],standard_accepted=sum(r['exit']==0 and not r['nonstandard_axioms'] and r['axiom_reports_complete'] and r['attempt'] not in rejected for r in a),maximum_peak_rss_kib=max(int(r['peak_rss_kib'] or 0) for r in a),all_recorded_swaps_zero=all(r['swaps']=='0' for r in a),target='not yet established',deployed_premises_before=5,deployed_premises_after=5)
(e/'RESUME6-BUDGET.json').write_text(json.dumps(budget,indent=2)+'\n');print('charged',len(a),'new sources',len(files),'matched',sum(bool(r['accepted_attempts']) for r in files),'forbidden',sum(bool(r['forbidden']) for r in files))
