import lzma,json,subprocess,re,hashlib,collections,importlib.util
from pathlib import Path
D=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('c',str(D.parent/'pv-mf-20261029/PV_MF_check.py'));c=importlib.util.module_from_spec(sp);sp.loader.exec_module(c)
mods=c.load('MODULES.json');rows=json.load(lzma.open(D/'rows9-input.json.xz'));stale=c.load('STALE.json');co=c.load('COHORTS.json');ej={x['module'].replace('/','.'):x['resolution']['path'] for x in co['selected'] if x.get('resolution')}
external=json.load(open(D/'external-object-manifest.json'));ext={x['module'].replace('/','.') for x in external}
idx=collections.defaultdict(set)
for p,m in mods.items():
 for i in m['imports']:idx[i['name']].update(i['candidates'])
# Explicit h6 same-cohort resolution for dlib; independently source-hashed against current HEAD.
dlib=json.load(open(D/'dlib-preflight-input.json'))
dlp={m.replace('/','.'):v['source_path'] for m,v in dlib['source_closure'].items() if not v.get('external')}
tree={ln.split('\t')[1]:ln.split('\t')[0].split()[-1] for ln in subprocess.check_output(['git','ls-tree','-r','HEAD'],text=True).splitlines()};proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE);cache={}
def source(p):
 if p not in tree:return None
 if p not in cache:
  proc.stdin.write((tree[p]+'\n').encode());proc.stdin.flush();h=proc.stdout.readline().split();b=proc.stdout.read(int(h[2]));proc.stdout.read(1);cache[p]=b
 return cache[p]
def imports(b):
 # Strip nested Lean block comments, line comments and quoted strings before import scanning.
 s=b.decode(errors='replace');s=re.sub(r'--[^\n]*','',s);depth=0;o=[];i=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2
  elif s[i:i+2]=='-/':depth-=1;i+=2
  else:
   if depth==0:o.append(s[i])
   i+=1
 return re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)', ''.join(o),re.M)
output=[]
for r in rows:
 if r['recount9_status'] not in ['CLOSED-ON-CANDIDATE','RESTORED']:continue
 cs=r.get('closing_statement9');roots=[];gaps=[];seen={};queue=[]
 if cs:queue.append((cs['module'],cs['path'],[cs['module']]))
 for w in r.get('import_witnesses9',[]):
  name=w['path'][0];poss=idx.get(name,set());p=ej.get(name)
  if not p and len(poss)==1:p=next(iter(poss))
  if p:queue.append((name,p,[name]));roots.append(name)
  else:gaps.append(dict(module=name,reason='audit root path ambiguous or absent',candidates=sorted(poss)))
 while queue:
  name,p,chain=queue.pop()
  if name in seen or name in ext:continue
  b=source(p)
  if b is None:gaps.append(dict(module=name,path=p,reason='authority-selected source absent at candidate'));continue
  imps=imports(b);seen[name]=dict(path=p,blob=tree[p],sha256=hashlib.sha256(b).hexdigest(),imports=imps,chain=chain)
  for n in imps:
   if n in ext:continue
   poss=idx.get(n,set());q=ej.get(n)
   if not q and name in dlp:q=dlp.get(n)
   if not q and len(poss)==1:q=next(iter(poss))
   if q:queue.append((n,q,chain+[n]))
   else:gaps.append(dict(module=n,chain=chain,reason='no unique EJR/h6/tracked source; freeze/h7 generation provenance required',candidates=sorted(poss)))
 hits=[dict(record=i+1,path=t['path'],chain=v['chain']) for i,t in enumerate(stale) for v in seen.values() if v['path']==t['path']]
 output.append(dict(id=r['id'],closing=cs,audit_roots=roots,modules=seen,gaps=gaps,hits=hits))
(D/'exact-traces.json').write_text(json.dumps(output,indent=2));print([(x['id'],len(x['modules']),len(x['gaps']),len(x['hits'])) for x in output])
