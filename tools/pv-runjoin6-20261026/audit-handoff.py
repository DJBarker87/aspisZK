"""One serial, split statement/axioms audit of the changed trust handoff.
New small modules, cached dependencies only; this is NOT a source closure replay.
The exact selected declarations are frozen before the first audit launch.
"""
from pathlib import Path
import sys,subprocess,re,json,hashlib
root=Path.cwd(); start=int(sys.argv[1]); end=26898
out=root/'evidence/pv-runjoin6-20261026'; formal=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
prior=(formal/'PV_RunJoin_CompleteEventStep.lean').read_text()
names=re.findall(r'^#print axioms (\S+)',prior,re.M)
# Inspect the actual published/source-native handoff first, then the generic
# source/control support. Each declaration occurs once in this campaign.
priority=('SourceSelectionContract','SelectedAdmission','InstalledFamily','InstalledEndpoint','NativeSelectedInputs','InstalledTransport','SourceBoundary','LedgerEndpoint','OsFailure','SelectedOsFailure','SelectedErrorPrelude','NativeEffect','LedgerBoundary')
names=sorted(dict.fromkeys(names),key=lambda n:(next((i for i,p in enumerate(priority) if p in n),len(priority)),n))
assert len(names)>=end-start+1
rows=[]
for attempt,name in zip(range(start,end+1),names):
 module=f'R1Z/PV_RunJoin_TrustAudit{attempt}'
 # The old declaration's owning namespace is also its import module here.
 dep='.'.join(name.split('.')[:-1])
 text=f'''import R1Z.PV_RunJoin_TrustEndpoint\nimport {dep}\nset_option autoImplicit false\n/- Cached exact-statement/axioms audit, not a new proof or a native instance. -/\n#check @{name}\n#print axioms {name}\n'''
 p=formal/(module.split('/')[1]+'.lean');p.write_text(text)
 rows.append(dict(attempt=attempt,target=module,declaration=name,source_sha256=hashlib.sha256(text.encode()).hexdigest(),kind='cached exact-statement/axioms audit; no premise-removal claim'))
(out/'handoff-audit-manifest.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),targets=rows,scope='single final split cached handoff audit after changed trust source; not dependency source replay'),indent=2)+'\n')
for row in rows:
 attempt=row['attempt'];module=row['target']
 proc=subprocess.run([sys.executable,'tools/pv-runjoin6-20261026/local-check.py',str(attempt),module],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 receipt=out/f'receipt-{attempt}.json'
 if not receipt.exists():
  print(proc.stdout[-3000:],flush=True);sys.exit(1)
 r=json.loads(receipt.read_text());print(json.dumps({k:r[k] for k in ['attempt','target','exit','wall_seconds','peak_rss_bytes','swaps','accepted']}),flush=True)
 # Evidence snapshots retain the exact checked source. Audit-only modules do
 # not become permanent members of the production formal module tree.
 (formal/(module.split('/')[1]+'.lean')).unlink()
 if not r['accepted']:
  print(proc.stdout[-3000:],flush=True);sys.exit(1)
