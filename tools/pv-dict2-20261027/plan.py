from pathlib import Path
import re,json,hashlib,subprocess
R=Path.cwd();E=R/'evidence/pv-dict2-20261027';D=R/'docs/research/v8-r0-zk-20261009/lean'
roots=['R1Z.PDict_RemainingDictionary231','R1Z.PDict_PureDictionary','R1Z.PDict_FinalTypes','R1Z.PDict_ArrayReference244','R1Z.PDict_OwnedCorrect262']
consumers=[]
for p in D.rglob('*.lean'):
 if not p.name.startswith('PDict_') and re.search(r'^import R1Z\.PDict_',p.read_text(),re.M):consumers.append(str(p.relative_to(D))[:-5].replace('/','.'))
roots+=consumers
# Rebuild's module resolution, never historical name lookup.
inv=json.loads((R/'evidence/envj-rebuild-20261026/EJR_final-inventory.json').read_text());res={x['module'].replace('/','.'):x['resolution'] for x in inv['selected'] if x.get('resolution')}
mods={};seen=set()
def visit(m):
 if m in seen:return
 seen.add(m);p=D/(m.replace('.','/')+'.lean')
 if m.startswith('R1Z.') and p.exists():
  data=p.read_bytes();authority='integrated candidate path'
 elif m in res:
  q=res[m];data=subprocess.check_output(['git','show','research:'+q['path']]);authority=dict(rebuild_resolution=q,research_path=q['path'])
 else:return
 s=data.decode();imports=re.findall(r'^import (\S+)',s,re.M);mods[m]=dict(module=m,source_sha256=hashlib.sha256(data).hexdigest(),path=str(p.relative_to(R)) if p.exists() else None,authority=authority,imports=imports)
 for c in imports:visit(c)
for m in roots:visit(m)
(E/'closure-plan.json').write_text(json.dumps(dict(roots=roots,consumers=consumers,modules=mods),indent=2)+'\n')
print('roots',len(roots),'modules',len(mods),'pdict',sum(m.startswith('R1Z.PDict') for m in mods))
