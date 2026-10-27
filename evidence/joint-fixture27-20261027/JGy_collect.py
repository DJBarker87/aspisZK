from pathlib import Path
import json,hashlib,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[json.loads(f.read_text()) for f in sorted(P.glob('JGy27_*/receipt.json'))]
(P/'JGy_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in rows))
passed=[r for r in rows if r['exit_status']==0];failed=[r for r in rows if r['exit_status']!=0]
assert all(set(re.findall(r'\[([^\]]*)\]',a)[-1].replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound',''} for r in passed for a in r['print_axioms'] if 'depends on axioms' in a)
valid={(name,h):r['attempt'] for r in passed for name,h in r['source_hashes'].items()}
manifest=[]
for f in sorted((R/'lean').glob('JGy_*.lean')):
 h=sha(f.read_bytes());manifest.append(dict(module=f.stem,source_sha256=h,source_bytes=f.stat().st_size,passing_attempt=valid.get((f.name,h)),status='checked' if (f.name,h) in valid else 'UNCHECKED'))
(P/'JGy_SOURCES.json').write_text(json.dumps(manifest,indent=2)+'\n')
summary=dict(lean_requests=len(rows),budget=100,kani_runs=0,kani_budget=60,passed=len(passed),failed=len(failed),wall_seconds=sum(r['wall_seconds'] for r in rows),peak_rss_kib=max(int(r['peak_rss_kib'] or 0) for r in rows),swaps=sum(int(r['swaps'] or 0) for r in rows),failures=[dict(attempt=r['attempt'],exit_status=r['exit_status'],module=r['sources']) for r in failed],checked_current_sources=sum(x['status']=='checked' for x in manifest),unchecked_current_sources=[x['module'] for x in manifest if x['status']!='checked'],standard_axioms_only_in_passes=True)
(P/'JGy_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
source=(R/'lean/FJv_Top.lean').read_bytes();before=(P/'JGy_FJv_Top_BEFORE.lean.txt').read_bytes();assert source==before
(P/'JGy_FJv_Top_AFTER.lean.txt').write_bytes(source)
(P/'JGy_LEDGER_DELTA.json').write_text(json.dumps(dict(target='AspisR1.FJv_Top.deployed',method='Quantified atomic-law-family/conjunction-leaf; shared witnesses, deployment rows, guards and carriers retained; authoritative latest FJv ledger row including separately booked L187',actual_before=dict(T=83,P=3,G=13,C=0),actual_after=dict(T=83,P=3,G=13,C=0),deployment_before=dict(T=89,P=18,G=13,C=0),deployment_after=dict(T=89,P=18,G=13,C=0),removed=dict(T=0,P=0,G=0,C=0),added=dict(T=0,P=0,G=0,C=0),changed=dict(T=0,P=0,G=0,C=0),source_sha256=sha(source),byte_identical=True,nonvacuity='Not yet established; local helper/resource results do not instantiate accepted1/accepted2 or full joint hypotheses'),indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='unchecked_current_sources'},indent=2))
