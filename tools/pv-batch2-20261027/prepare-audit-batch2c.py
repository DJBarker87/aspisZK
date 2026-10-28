from pathlib import Path
import json,re,hashlib
E=Path('evidence/pv-batch2-20261027/batch2c');L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');t=json.loads((E/'TALLY.json').read_text());assert t['lean_charged']==97
latest={}
for a in t['attempts']:
 p=E/f"{a['id']}.json"
 if p.exists():
  r=json.loads(p.read_text());latest[r['module']]=r
kept=[];drafts=[]
for p in sorted(L.glob('PV_B2_C_*.lean')):
 if 'Audit' in p.stem:continue
 m='R1Z/'+p.stem;r=latest.get(m);sha=hashlib.sha256(p.read_bytes()).hexdigest()
 if r and r['exit_status']==0 and r['accepted_axioms'] and r['source_sha256']==sha:
  names=r['parsed_axioms'];missing=[n for n in re.findall(r'(?m)^(?:private )?theorem (\S+)',p.read_text()) if not any(d['declaration'].endswith('.'+n) for d in names)]
  # Private helper theorems are audited through every consuming public declaration.
  public=[n for n in re.findall(r'(?m)^theorem (\S+)',p.read_text()) if n in missing];assert not public,(m,public)
  kept.append(dict(module=m,source_sha256=sha,attempt=r['attempt'],declarations=names,private_helpers_audited_transitively=missing,dependency_objects=r['dependency_objects']))
 else:
  q=E/'drafts'/(p.name+'.txt');q.parent.mkdir(exist_ok=True);q.write_bytes(p.read_bytes());p.unlink();drafts.append(dict(module=m,sha256=sha,archive=str(q),last_attempt=r['attempt'] if r else None))
assert all(set(d['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in kept for d in r['declarations'])
groups={'Sampler':[],'Weights':[]}
for r in kept:
 group='Sampler' if any(x in r['module'] for x in ['Gamma','Sampler','AddSmall','MachineArithmetic','U32Arithmetic','NativeGamma']) else 'Weights';groups[group].append(r)
for family,rows in groups.items():
 names=sorted({d['declaration'] for r in rows for d in r['declarations']});s=''.join('import '+r['module'].replace('/','.')+'\n' for r in rows)+'\n'+''.join('#print axioms '+n+'\n' for n in names);(L/f'PV_B2_C_Audit{family}.lean').write_text(s)
allnames=sorted({d['declaration'] for r in kept for d in r['declarations']})
(L/'PV_B2_C_AuditManifest.lean').write_text('import R1Z.PV_B2_C_AuditSampler\nimport R1Z.PV_B2_C_AuditWeights\n'+''.join('#print axioms '+n+'\n' for n in allnames))
(E/'AUDIT-PREFLIGHT.json').write_text(json.dumps(dict(scope='partial batch2c source-law manifest; no privacy endpoint closure claim',accepted=kept,drafts=drafts,declarations=len(allnames),charged=97,audit_ids=[52397,52398,52399],all_public_theorems_covered=True),indent=2)+'\n');print('frozen',len(kept),'modules;',len(allnames),'printed declarations;',len(drafts),'drafts archived')
