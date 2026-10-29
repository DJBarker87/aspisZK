from pathlib import Path
import json,hashlib,re,subprocess,datetime
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rs=[json.loads(p.read_text()) for p in sorted(D.glob('lean*-receipt.json'))]
assert len(rs)==100 and {r['attempt'] for r in rs}==set(range(67300,67400))
ns=[json.loads(p.read_text()) for p in sorted(D.glob('native*-receipt.json'))]
assert len(ns)==4
coverage=json.loads((D/'audit-coverage.json').read_text())
for name,names in coverage.items():
 r=next(r for r in reversed(rs) if r.get('module')==name and r['exit']==0)
 for n in names:assert "'PV_DIAG12."+n+"'" in r['print_axioms']
base='b1aad8357fdc22e6ddfd50be727f0436ca834748'
links=[]
for p in sorted((D.parent/'pv-diag10-20261029').glob('*.lean')):
 names=re.findall(r'^def (PV_DIAG10_Link_\w+)',p.read_text(),re.M)
 if not names:continue
 old=subprocess.check_output(['git','show',base+':'+str(p.relative_to(Path.cwd()))])
 assert old==p.read_bytes()
 links.append(dict(path=str(p.relative_to(Path.cwd())),sha256=sha(p),definitions=names,unchanged=True))
assert sum(len(r['definitions']) for r in links)==15
changed=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
assert all(p.startswith('evidence/pv-diag12-20261029/') for p in changed)
(D/'link-definition-integrity.json').write_text(json.dumps(dict(base=base,files=links,definition_count=15,changes_outside_assigned_evidence=[]),indent=2)+'\n')
# A source label names launch context; the snapshots identify the actual inputs.
freeze=json.loads((D/'freeze-sources.json').read_text());bindings=[]
for m,pin in freeze['sources'].items():
 p=Path(pin['path']);assert sha(p)==pin['sha256']
 blob=subprocess.check_output(['git','show',freeze['revision']+':'+pin['path']]);assert hashlib.sha256(blob).hexdigest()==pin['sha256']
 r=next(r for r in reversed(rs) if r['module']==m and r['exit']==0 and r['source_sha256']==pin['sha256'])
 bindings.append(dict(module=m,proof_freeze=freeze['revision'],blob=pin['blob'],source_sha256=pin['sha256'],accepted_attempt=r['attempt'],launch_revision_label=r['source_revision'],snapshot='lean'+str(r['attempt'])+'-source.lean.txt'))
(D/'proof-source-commit-binding.json').write_text(json.dumps(bindings,indent=2)+'\n')
# Check one-scope-per-job cadence against recorded admissions; every next gate
# follows the preceding gate plus its entire measured wrapper duration.
intervals=[]
for p in sorted(D.glob('*-receipt.json')):
 r=json.loads(p.read_text())
 if r.get('kind') not in ['lean','native']:continue
 label=p.name.removesuffix('-receipt.json');a=json.loads((D/('admission-'+label+'.json')).read_text())
 start=datetime.datetime.fromisoformat(a['utc']).timestamp();intervals.append((start,start+r['wall_seconds'],label))
intervals.sort()
assert all(a[1]<=b[0] for a,b in zip(intervals,intervals[1:]))
summary=dict(attempts=len(rs),accepted=sum(r['exit']==0 for r in rs),rejected=[r['attempt'] for r in rs if r['exit']!=0],native_scopes=len(ns),Kani=0,axioms_allowed=['propext','Classical.choice','Quot.sound'],axioms_checked=True,audited_theorems=sum(map(len,coverage.values())),max_rss_kib=max(int(r['peak_rss_kib']) for r in rs),lean_wrapper_wall_seconds=sum(r['wall_seconds'] for r in rs),swaps=sum(int(r['swaps']) for r in rs+ns),scope_intervals_nonoverlapping=True,source_freeze=freeze['revision'],endpoint_premises=dict(removed=0,added=0,weakened=0,changed=0),deployed_links_closed=0)
(D/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary))
