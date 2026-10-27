from pathlib import Path
import subprocess,json,re,hashlib,collections
P=Path(__file__).resolve().parent; pins=json.loads((P/'pins.json').read_text());manifest=json.loads((P/'manifest.json').read_text()); bypath={(x['ref'],x['path']):x for x in manifest}; used=set()
def read(k,path):
 key=(k,path)
 if key in bypath:
  x=bypath[key];used.add(key);return (P/x['snapshot']).read_text()
 try: raw=subprocess.check_output(['git','show',pins[k]+':'+path],stderr=subprocess.DEVNULL)
 except subprocess.CalledProcessError:return None
 out=P/'snapshots'/k/path
 if path.endswith('.lean'):out=Path(str(out)+'.txt')
 out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(raw)
 x=dict(ref=k,revision=pins[k],path=path,sha256=hashlib.sha256(raw).hexdigest(),snapshot=str(out.relative_to(P)));bypath[key]=x;manifest.append(x);used.add(key);return raw.decode()
R='docs/research/v8-r0-zk-20261009/lean/'
# Graph uses only imports, never audit roots. Every edge is backed by pinned git source.
graphs={}
for k in pins:
 graph={}
 for x in manifest:
  if x['ref']==k and x['path'].startswith(R) and x['path'].endswith('.lean'):
   module=x['path'][len(R):-5].replace('/','.');s=(P/x['snapshot']).read_text()
   graph[module]=re.findall(r'^import\s+(\S+)',s,re.M)
 graphs[k]=graph
roots=[('research','R1Z.PrivacyR1HeadlineDeployedReal'),('join','R1Z.PV_Join_AggregateCaller'),('join','R1Z.PV_Join_PublicCaller'),('rw','R1Z.ProverRw19CanonicalAuditRefinement'),('rw','R1Z.ProverRw18ContextData')]
closures=[]
fallbacks=[]
for key,root in roots:
 queue=[root];paths={root:[root]};missing=[]
 for m in queue:
  if m not in graphs[key]:
   path=R+m.replace('.','/')+'.lean'
   s=read(key,path)
   if s is None and m.startswith('R1Z.ProverRwFull'):
    path='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/'+m.split('.')[-1]+'.lean';s=read(key,path)
   if s is None and m.startswith('R1Z.PDict_'):
    s=read('dict',R+m.replace('.','/')+'.lean');fallbacks.append(dict(consumer_ref=key,module=m,source_ref='dict',reason='module absent from candidate git; pinned dictionary source resolves import graph only, object association not certified'))
   if s is not None:graphs[key][m]=re.findall(r'^import\s+(\S+)',s,re.M)
   else:
    if m.startswith(('R1Z.','R0Z.')):missing.append(m)
    continue
  for dep in graphs[key][m]:
   if dep not in paths:paths[dep]=paths[m]+[dep];queue.append(dep)
 closures.append(dict(ref=key,root=root,paths=paths,unresolved_project_modules=missing))
(P/'import-fallbacks.json').write_text(json.dumps(fallbacks,indent=2)+'\n')
(P/'import-closures.json').write_text(json.dumps(closures,indent=2)+'\n')
# Preserve every original row statement/class; independently resolve and compare definition objects.
rows=json.loads((P.parent/'recount2/rows2.json').read_text());prev={x['id']:x for x in json.loads((P.parent/'recount2/resolved-definitions.json').read_text())};aud=[]
for row in rows:
 d=row.get('definition','');path,_,decl=d.partition('#');loc=[]
 for key in pins:
  if not path:continue
  s=read(key,path)
  if s is not None:
   sha=hashlib.sha256(s.encode()).hexdigest();line=None
   if decl:
    match=re.search(r'^(?:[^\n]*\b(?:theorem|def|abbrev|structure|class)\s+[^\n]*'+re.escape(decl.split('/')[-1])+r'[^\n]*)',s,re.M)
    if match:line=s[:match.start()].count('\n')+1
   loc.append(dict(ref=key,path=path,sha256=sha,declaration=decl,line=line))
 # Full source comparisons, not proof-name guesses; inherited audits remain historical evidence.
 old=prev.get(row['id'],{}).get('resolved',{});aud.append(dict(id=row['id'],definition=d,sources=loc,recount2_sha256=old.get('sha256'),same_as_recount2=any(x['sha256']==old.get('sha256') for x in loc)))
(P/'definition-audit3.json').write_text(json.dumps(aud,indent=2)+'\n')
(P/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');(P/'used-sources.json').write_text(json.dumps(sorted(used),indent=2)+'\n')
print('Resolved',sum(bool(x['sources']) for x in aud),'rows; unchanged definition available',sum(x['same_as_recount2'] for x in aud));print([(c['ref'],c['root'],len(c['paths']),c['unresolved_project_modules']) for c in closures])
