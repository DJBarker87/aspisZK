from pathlib import Path
import re,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin62-20261029';plan=json.loads((E/'build-plan.json').read_text());accepted={v['module'] for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted']};groups=[[],[],[]];expected=[]
for m in sorted(accepted):
 if not m.startswith('R1Z.PV_RunJoin_') or not m.endswith('62') or 'Audit' in m:continue
 p=R/plan['modules'][m]['path'];s=p.read_text();
 if not re.search(r'^namespace (\S+)',s,re.M):continue
 namespace=re.search(r'^namespace (\S+)',s,re.M)[1];decls=re.findall(r'^(?:@\[[^\n]*\]\s*)?(?:def|abbrev|theorem) (\w+)',s,re.M);i=0 if m.endswith('CircleBinding62') else 1 if any(x in m for x in ['NativeResidual','NativeFrames','NativeActual','NativeOrigin','NativeObstruction']) else 2
 groups[i].append((m,[namespace+'.'+d for d in decls]));expected.extend(namespace+'.'+d for d in decls)
for i,g in enumerate(groups,1):
 s='\n'.join('import '+m for m,_ in g)+'\nset_option autoImplicit false\n\n'+'\n'.join('#print axioms '+d for _,ds in g for d in ds)+'\n';p=R/f'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_Audit{i}_62.lean';p.write_text(s)
(E/'axioms-expected.json').write_text(json.dumps(dict(expected=expected,groups=groups),indent=2)+'\n');print('Audit declarations',len(expected),'modules',sum(map(len,groups)))
