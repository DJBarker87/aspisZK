"""Freeze checked rw21 sources plus the existing 230-declaration component.
Run only after focused work; --check is compile-free and detects source drift.
Three distinct final audit modules are emitted, never a clean-source claim.
"""
from pathlib import Path
import hashlib,json,re,subprocess,sys
r=Path(__file__).resolve().parents[3];d=r/'docs/research/v8-r0-zk-20261009/lean/R1Z';e=r/'evidence/pv-rw21-20261027'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=e/'frozen-component-inputs.json'
if '--check' in sys.argv:
 x=json.loads(manifest.read_text())
 for p in x['modules']:assert sha(r/p['path'])==p['source_sha256'],p['module']
 for p in x['audit_modules']:assert sha(r/p['path'])==p['source_sha256'],p['module']
 print('frozen inputs match',len(x['modules']),'rw21 modules');raise SystemExit
latest={}
for p in sorted(e.glob('37???-receipt.json')):
 x=json.loads(p.read_text())
 if x.get('charged'):latest[x['module']]=x
rows=[];names=[]
for p in sorted(d.glob('ProverRw21*.lean')):
 if p.stem in ['ProverRw21ComponentInputs','ProverRw21AxiomsAudit','ProverRw21FrozenManifest']:continue
 module='R1Z.'+p.stem;x=latest.get(module)
 assert x and x['exit_status']==0 and x['source_sha256']==sha(p),('not checked current source',module)
 source=p.read_text();ns=re.search(r'^namespace (R1Z[\w.]*)$',source,re.M)
 assert ns,p
 audits=re.findall(r'^#print axioms ([\w.]+)$',source,re.M)
 declared=re.findall(r'^theorem (\w+)',source,re.M)
 assert set(declared)<=set(audits),(module,'missing theorem audit',set(declared)-set(audits))
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',source),(module,'forbidden token')
 for name in audits:names.append(name if name.startswith('R1Z.') else ns[1]+'.'+name)
 rows.append(dict(module=module,path=str(p.relative_to(r)),source_sha256=sha(p),attempt=x['attempt'],axioms_declarations=names[-len(audits):] if audits else []))
old=json.loads((r/'evidence/pv-rw19-resume-20261026/frozen-component-inputs.json').read_text())
allnames=list(dict.fromkeys(old['audit_declarations']+names))
imports=['import R1Z.ProverRw19FrozenManifest']+['import '+x['module'] for x in rows]
comment='-- Cached component audit; no clean-source dependency rebuild or privacy target claim.\n'
texts={
 'ProverRw21ComponentInputs':'\n'.join(imports)+'\n'+comment+'\n'.join('#check '+n for n in allnames)+'\n',
 'ProverRw21AxiomsAudit':'import R1Z.ProverRw21ComponentInputs\n'+comment+'\n'.join('#print axioms '+n for n in allnames)+'\n',
 'ProverRw21FrozenManifest':'import R1Z.ProverRw21AxiomsAudit\n'+comment+'\n'.join('#check '+n for n in ['R1Z.ProverRw21ModelInstance','R1Z.ProverRw21CallerCriterion.criterion','R1Z.ProverRw19P6ContextIdentity.identity'])+'\n'}
audit=[]
for name,source in texts.items():
 p=d/(name+'.lean');p.write_text(source);audit.append(dict(module='R1Z.'+name,path=str(p.relative_to(r)),source_sha256=sha(p)))
manifest.write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip(),modules=rows,axioms=allnames,audit_modules=audit,classification='cached-component replay; not clean-source rebuild; deployed protocol and source association remain explicit obligations',prior_manifest=old['manifest_source_sha256']),indent=2)+'\n')
print(len(rows),'rw21 modules,',len(allnames),'combined declarations')
