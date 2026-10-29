import json,importlib.util,lzma,collections
from pathlib import Path
D=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('c',str(D.parent/'pv-mf-20261029/PV_MF_check.py'));c=importlib.util.module_from_spec(s);s.loader.exec_module(c)
mods=c.load('MODULES.json');stale=c.load('STALE.json');rows=json.loads((D/'rows9-input.json').read_text());out=[]
for r in rows:
 if r['recount9_status'] not in ['CLOSED-ON-CANDIDATE','RESTORED']:continue
 cs=r.get('closing_statement9'); roots=[]
 if cs:roots.append(cs['path'])
 for w in r.get('import_witnesses9',[]):
  for n in w['path'][:1]:
   # Module witnesses are used only for a conservative candidate graph at this stage.
   roots.extend(p for p in mods if p.endswith('/'+n.replace('.','/')+'.lean') or ('.' not in n and Path(p).stem==n))
 seen={};queue=[(p,[p]) for p in roots]
 while queue:
  p,chain=queue.pop()
  if p in seen:continue
  seen[p]=chain
  for i in mods.get(p,{}).get('imports',[]):
   queue.extend((q,chain+[q]) for q in i['candidates'])
 hits=[{'record':i+1,'path':t['path'],'chain':seen[t['path']]} for i,t in enumerate(stale) if t['path'] in seen]
 out.append({'id':r['id'],'closing':cs,'roots':roots,'candidate_path_count':len(seen),'hits':hits})
(D/'candidate-traces.json').write_text(json.dumps(out,indent=2))
for r in out:
 print(r['id'],r['candidate_path_count'],len(r['hits']),sorted(set(x['path'].split('/')[-1] for x in r['hits'])))
