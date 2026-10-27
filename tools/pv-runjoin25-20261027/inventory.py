"""Refresh own source pins, enumerate consumer uses, and record closure boundaries."""
from pathlib import Path
import json,hashlib,subprocess,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin25-20261027'
r=json.loads((E/'focused-resolution.json').read_text());s={}
for m,v in r['resolved'].items():
 if 'imports' in v:
  b=subprocess.check_output(['git','cat-file','blob',v['git_blob']]);assert hashlib.sha256(b).hexdigest()==v['sha256'];s[m]=b.decode()
prior=json.loads((R/'evidence/pv-runjoin24-20261027/focused-resolution.json').read_text())
prior_sources={}
for m,v in prior['resolved'].items():
 if m not in r['resolved']:
  r['resolved'][m]=v
  if 'imports' in v:
   b=subprocess.check_output(['git','cat-file','blob',v['git_blob']]);assert hashlib.sha256(b).hexdigest()==v['sha256'];s[m]=b.decode()
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();refresh=[]
for path in sorted((R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_RunJoin_*25.lean')):
 rel=str(path.relative_to(R));m='R1Z.'+path.stem;b=subprocess.check_output(['git','show',head+':'+rel]);blob=subprocess.check_output(['git','rev-parse',head+':'+rel],text=True).strip();imports=re.findall(r'^import\s+(\S+)',b.decode(),re.M)
 assert all(x in r['resolved'] for x in imports),(m,imports)
 v=dict(authority='h5 own git-tracked HEAD',revision=head,path=rel,git_blob=blob,sha256=hashlib.sha256(b).hexdigest(),imports=imports,tracked_conflicts=[])
 r['resolved'][m]=v;s[m]=b.decode();refresh.append(dict(module=m,**v))
r['head']=head;(E/'focused-resolution.json').write_text(json.dumps(r,indent=2)+'\n');(E/'final-source-refresh.json').write_text(json.dumps(refresh,indent=2)+'\n')
def closure(root):
 seen=set();todo=[root]
 while todo:
  m=todo.pop()
  if m in seen:continue
  seen.add(m);todo.extend(r['resolved'].get(m,{}).get('imports',[]))
 return seen
roots=['R1Z.PrivacyR1HeadlineDeployedReal','R1Z.PV_Src_ReleaseAudit','R1Z.PV_Src_RootDynamicIdentification','R1Z.BuilderRuntimeJoin','R1Z.PV_RunJoin_ConsumerAudit25']
out={}
for root in roots:
 c=closure(root);hits=[]
 for m in sorted(c):
  lines=[dict(line=i,text=l) for i,l in enumerate(s.get(m,'').splitlines(),1) if re.search(r'\bSourceIdentification\b|\bBuilderSource\.',l)]
  if lines:hits.append(dict(module=m,sha256=r['resolved'][m]['sha256'],authority=r['resolved'][m]['authority'],uses=lines))
 out[root]=dict(project_module_count=sum(m in s for m in c),uses=hits)
(E/'consumer-use-inventory.json').write_text(json.dumps(out,indent=2)+'\n')
print('Pinned',len(refresh),'new modules;',len(s),'total project sources; unpinned',r['unpinned'])
