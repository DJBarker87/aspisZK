"""Audit the exact accepted combined private closure; exclude rejected candidates."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path('evidence/pv-batch2-20261027/batch2e');D=E.parent/'batch2d';L=Path('docs/research/v8-r0-zk-20261009/lean');modules={}
for a in json.loads((D/'ACCEPTED-PROGRESS.json').read_text())['sources']:
 modules[a['module']]=dict(a,provenance='batch2d accepted snapshot')
for p in sorted(E.glob('398[0-9][0-9].json')):
 a=json.loads(p.read_text())
 if a.get('exit_status')==0 and a.get('accepted_axioms'):
  hp=json.loads((E/'H5-SOURCE-PINS.json').read_text()).get(a['module'])
  modules[a['module']]=dict(module=a['module'],path=hp['path'] if hp else str(L/(a['module']+'.lean')),source_sha256=a['source_sha256'],declarations=a['parsed_axioms'],attempt=a['attempt'],provenance='batch2e successful current source')
imports=[];decls=[];rows=[]
for m,a in modules.items():
 p=Path(a['path']);sha=hashlib.sha256(p.read_bytes()).hexdigest();assert sha==a['source_sha256'],(m,'uncompiled source edit')
 if m in ['R1Z/ProverRwFullTypes','R1Z/ProverRwFullExternalTypes','R1Z/ProverRwFullExternalFuns']:p=Path(json.loads((E/'H5-SOURCE-PINS.json').read_text())[m]['path'])
 imports.append(m.replace('/','.'))
 ds=a['declarations']
 for d in ds:
  n=d.get('declaration')
  if not n or n.startswith('_private') or '._private' in n:continue
  if n not in decls:decls.append(n)
 rows.append(dict(module=m,path=str(p),source_sha256=sha,attempt=a['attempt'],provenance=a['provenance']))
p=L/'R1Z/PV_B2_E_AuditCombined.lean';s='\n'.join('import '+m for m in imports)+'\n\n-- Every closing theorem and accepted public predecessor; private helper audits remain in original receipts.\n'+'\n'.join('#print axioms '+n for n in decls)+'\n';p.write_text(s)
(E/'AUDIT-PREFLIGHT.json').write_text(json.dumps(dict(sources=rows,public_declarations=decls,imports=imports,private_helpers='direct prior axiom outputs retained; all public dependencies audited transitively',new_rows='only a source/row candidate audit; no endpoint/deployment closure claim'),indent=2)+'\n');print(len(imports),'imports',len(decls),'public audits')
