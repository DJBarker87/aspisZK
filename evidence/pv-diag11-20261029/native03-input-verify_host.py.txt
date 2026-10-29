from pathlib import Path
import json,hashlib,re,sys,subprocess
D=Path('/home/dombarker/project-offloads/codex-pv-diag11-20261029')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
phase=sys.argv[1]
ext=json.loads((D.parent/'codex-pv-diag5-20261029/external-authority.json').read_text())
for r in ext:assert sha(Path(r['path']))==r['object_sha256']
reuse=json.loads((D/'reuse.json').read_text())['rows']
for r in reuse:
 assert sha(Path(r['path']))==r['sha256'];assert sha(Path(r['source']))==r['source_sha256']
records=[]
for p in sorted(D.glob('lean*-receipt.json')):
 r=json.loads(p.read_text());assert r['admission_exit']==0 and r['admission_allowed'] is True
 assert r['swaps']=='0'
 assert sha(D/(p.name.replace('-receipt.json','-source.lean.txt')))==r['source_sha256']
 if r['exit']==0:
  assert 'sorryAx' not in r['print_axioms']
  for ax in re.findall(r'depends on axioms: \[([^]]*)\]',r['print_axioms']):assert set(ax.split(', '))<={'propext','Classical.choice','Quot.sound'}
 records.append(r)
freeze=json.loads((D/'freeze-sources.json').read_text());matched=[]
for m,pin in freeze['sources'].items():
 p=D/'sources'/(m+'.lean');assert sha(p)==pin['sha256']
 hits=[r for r in records if r['module']==m and r['exit']==0 and r['source_sha256']==sha(p)]
 if not hits:
  assert phase=='preaudit' and m in {'PV_DIAG11_Audit','PV_DIAG11_ProducerAudit','PV_DIAG11_FinalManifest'},m
  continue
 r=hits[-1];obj=D/'objects'/(m+'.olean');assert sha(obj)==r['object_sha256'],m
 for files in r['dependency_objects'].values():
  for path,h in files.items():assert sha(Path(path))==h,(m,path)
 matched.append(dict(module=m,attempt=r['attempt'],source=pin,object_sha256=sha(obj)))
# Additional source provenance: constructor source and logger mutation surface,
# not a claim to have proved PC/unwinder/resolver association.
anyhow=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/anyhow-1.0.104/src/error.rs')
assert sha(anyhow)==sha(D/'source-anyhow-error.rs.txt')
if phase=='preaudit':
 S=D.parent/'codex-pv-fscan-20261028/src';root=S/'tools/r1-cost-probe';lock=root/'Cargo.lock';before=sha(lock)
 cmd=['/home/dombarker/.cargo/bin/cargo','+1.94.1','metadata','--locked','--offline','--format-version','1','--manifest-path',str(root/'Cargo.toml'),'--filter-platform','x86_64-unknown-linux-gnu','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover']
 p=subprocess.run(cmd,cwd=root,text=True,capture_output=True)
 assert sha(lock)==before
 (D/'feature-metadata-stderr.log').write_text(p.stderr)
 meta=dict(command=cmd,exit=p.returncode,lock_sha256=before,profile='release (source-selection setting; metadata itself does not compile)',compiler='1.94.1',compiler_preservation='V370 / D381 / D386 retained')
 if p.returncode==0:
  data=json.loads(p.stdout);packages={p['id']:p for p in data['packages']}
  meta['crates']=[dict(name=packages[n['id']]['name'],version=packages[n['id']]['version'],id=n['id'],features=n['features'],dependencies=n['dependencies']) for n in data['resolve']['nodes']]
 else:
  meta['status']='feature resolution unavailable; no complete deployed-feature binding claimed';meta['error']=p.stderr
 (D/'resolved-features.json').write_text(json.dumps(meta,indent=2)+'\n')
report=dict(phase=phase,external_checked=len(ext),reused_project_objects=len(reuse),frozen_revision=freeze['revision'],current_sources=matched,attempts=len(records),accepted=sum(r['exit']==0 for r in records),rejected=[r['attempt'] for r in records if r['exit']!=0],mismatches=[],scope='focused source-control modules plus unchanged diagnostic/runjoin cohort; no privacy-release replay')
(D/('verification-'+phase+'.json')).write_text(json.dumps(report,indent=2)+'\n')
print('verified',phase,'sources',len(matched),'external',len(ext),'reuse',len(reuse),'attempts',len(records))
