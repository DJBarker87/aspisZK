from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin63-20261029'
accepted={v['module']:v for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text()) if v['accepted']}
items=[]
for m,v in sorted(accepted.items()):
 if not m.startswith('R1Z.PV_RunJoin_') or not m.endswith('63') or 'Audit' in m:continue
 p=R/v['source']['path'];b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==v['source_sha256'],m
 s=b.decode();ns=re.findall(r'^namespace\s+(R1Z\.PV_RunJoin_\w+)',s,re.M)[0]
 names=re.findall(r'^(?:@\[[^\n]*\]\s*)?(?:def|abbrev|theorem|structure|inductive)\s+(\w+)',s,re.M)
 items.append(dict(module=m,names=[ns+'.'+n for n in names]))
groups=[items[i::3] for i in range(3)];expected=[]
for i,group in enumerate(groups,1):
 m=f'R1Z.PV_RunJoin_Audit{i}_63';p=R/'docs/research/v8-r0-zk-20261009/lean'/(m.replace('.','/')+'.lean')
 names=[n for v in group for n in v['names']]
 p.write_text('\n'.join('import '+v['module'] for v in group)+'\n\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
 expected.append(dict(module=m,attempt=73496+i,imports=[v['module'] for v in group],names=names))
(E/'axioms-expected.json').write_text(json.dumps(expected,indent=2)+'\n')
print('audit declarations',sum(len(v['names']) for v in expected),'modules',len(items))
