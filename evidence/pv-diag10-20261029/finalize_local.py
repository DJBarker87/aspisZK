from pathlib import Path
import json,hashlib,subprocess,re
D=Path(__file__).resolve().parent.relative_to(Path.cwd())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lean=[json.loads(p.read_text()) for p in sorted(D.glob('lean*-receipt.json'))]
native=[json.loads(p.read_text()) for p in sorted(D.glob('native*-receipt.json'))]
assert len(lean)==100 and [r['attempt'] for r in lean]==list(range(66700,66800))
failed=set()
for r in lean:
 assert r['source_sha256'] not in failed,'unchanged failed source'
 if r['exit']:failed.add(r['source_sha256'])
 assert r['admission_exit']==0 and r['admission_allowed'] and r['swaps']=='0'
 assert sha(D/f"lean{r['attempt']}-source.lean.txt")==r['source_sha256']
 if not r['exit']:assert 'sorryAx' not in r['print_axioms']
for r in native:assert r['admission_exit']==0 and r['admission_allowed'] and r['exit']==0
freeze='de348ad8e7';sources=[]
for p in sorted(D.glob('PV_DIAG10_*.lean')):
 data=subprocess.check_output(['git','show',freeze+':'+str(p)])
 assert hashlib.sha256(data).hexdigest()==sha(p)
 accepted=[r for r in lean if r['module']==p.stem and r['exit']==0 and r['source_sha256']==sha(p)]
 assert accepted,p
 sources.append(dict(path=str(p),source_sha256=sha(p),freeze_revision=freeze,accepted_attempt=accepted[-1]['attempt']))
(D/'proof-source-commit-binding.json').write_text(json.dumps(sources,indent=2)+'\n')
audit='\n'.join(r['print_axioms'] for r in lean if r['attempt']>=66797)
for p in D.glob('PV_DIAG10_*.lean'):
 for name in re.findall(r'^theorem\s+(\w+)',p.read_text(),re.M):assert "'PV_DIAG10."+name+"'" in audit,name
assert all(p.stat().st_size<=20*1024*1024 for p in D.rglob('*') if p.is_file())
summary=dict(branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip(),base='2d083b9a42',proof_source_freeze=freeze,lean_attempts=len(lean),accepted=sum(r['exit']==0 for r in lean),rejected=[r['attempt'] for r in lean if r['exit']],native_scopes=len(native),kani=0,peak_rss_kib=max(int(r['peak_rss_kib']) for r in lean+native),swaps=sum(int(r['swaps']) for r in lean+native),lean_wrapper_wall_seconds=sum(r['wall_seconds'] for r in lean),audits=[{k:r[k] for k in ['attempt','module','exit','gnu_wall','peak_rss_kib','swaps','source_revision']} for r in lean if r['attempt']>=66797],new_theorems=json.loads((D/'audit-coverage.json').read_text())['new_theorems'],removed_endpoint_premises=0,source_binding_mismatches=0,cohorts='runjoin and b3p separately checked; no combined coherent release replay claimed')
(D/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
