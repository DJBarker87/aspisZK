from pathlib import Path
import subprocess,json,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin60-20261029';D=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
accepted={v['module']:dict(attempt=int(p.stem.split('-')[1]),**v) for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text()) if v['accepted']}
paths=subprocess.check_output(['git','diff','--name-only','03b847790d','HEAD'],cwd=R,text=True).splitlines()
modules=[]
for path in paths:
 if not path.endswith('.lean') or '/lean/R1Z/' not in path:continue
 m='R1Z.'+Path(path).stem
 if m.endswith(('ProofAudit60','FieldsAudit60','NodeAudit60')):continue
 b=(R/path).read_bytes();v=accepted.get(m)
 assert v and hashlib.sha256(b).hexdigest()==v['source_sha256'],('compile current source before audit',m)
 ns=re.search(r'^namespace (\S+)',b.decode(),re.M)[1]
 names=[ns+'.'+n for n in re.findall(r'^theorem\s+(\w+)',b.decode(),re.M)]
 if 'fun_pair_bound' in b.decode():names.append(ns+'.loop_bound.fun_pair_bound')
 modules.append(dict(module=m,path=path,theorems=names,accepted_attempt=v['attempt'],source_sha256=v['source_sha256']))
coverage=[]
for k,name in enumerate(['PV_RunJoin_ProofAudit60','PV_RunJoin_FieldsAudit60','PV_RunJoin_NodeAudit60']):
 group=modules[k::3];s='\n'.join('import '+v['module'] for v in group)+'\nset_option autoImplicit false\n'
 for v in group:
  s+='\n'+'\n'.join('#print axioms '+n for n in v['theorems'])+'\n'
 (D/(name+'.lean')).write_text(s)
 coverage.append(dict(audit='R1Z.'+name,modules=group))
(E/'axioms-coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
print('Audit coverage',len(modules),'modules',sum(len(v['theorems']) for v in modules),'theorems')
