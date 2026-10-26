"""Resolve the recursive dependency frontier using unique committed source hashes."""
from pathlib import Path
import json,subprocess,re,hashlib,collections,shlex
O=Path(__file__).parent
remote='''from pathlib import Path
import json
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
rs=json.loads((T/'EJR_all-restored-sources.json').read_text())
for p in T.glob('EJS_*-sources.json'):rs.extend(json.loads(p.read_text()))
print(json.dumps(dict(known=sorted({r['module'] for r in rs}),progress=json.loads((T/'EJR_progress.json').read_text()))))
'''
state=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(remote)],text=True));known=set(state['known'])
old=json.load(open(O.parent/'envj-rebuild-20261026/EJR_final-inventory.json'));excluded={r['module'] for r in old['unresolved_selected']}|{'R1Z/EventsR1P2','R1Z/SimCostOuterRetry6'}
index=collections.defaultdict(dict);valid=re.compile(r'[A-Za-z_\d][\w]*(?:/[\w]+)*');sha_re=re.compile('[0-9a-f]{64}')
def add(m,s,p,c):
 if not isinstance(s,str) or not sha_re.fullmatch(s) or not valid.fullmatch(m):return
 if s not in index[m]:index[m][s]=dict(evidence=p,context=c)
def walk(x,p):
 if isinstance(x,list):
  for v in x:walk(v,p)
 elif isinstance(x,dict):
  m=x.get('module',x.get('name'));s=x.get('source_sha256')
  if isinstance(m,str) and s:add(m.removesuffix('.lean').replace('.','/'),s,p,'explicit module/source_sha256')
  for key in ['source','source_path','path','file','frozen_source','src']:
   path=x.get(key)
   if isinstance(path,str) and path.endswith(('.lean','.lean.txt')):
    parts=path.removesuffix('.txt').removesuffix('.lean').split('/')
    for n in range(1,min(len(parts),8)+1):add('/'.join(parts[-n:]),x.get('source_sha256',x.get('sha256')),p,key+'='+path)
  for v in x.values():
   if isinstance(v,(dict,list)):walk(v,p)
files=subprocess.check_output(['git','ls-files'],text=True).splitlines();scanned=0
for p in files:
 if not p.endswith(('.json','.jsonl')) or p.startswith(('evidence/envj-rebuild','evidence/privacy-recount-')):continue
 try:
  raw=Path(p).read_text()
  if 'source_sha256' not in raw and '.lean' not in raw:continue
  ds=[json.loads(l) for l in raw.splitlines() if l.strip()] if p.endswith('.jsonl') else [json.loads(raw)]
  for x in ds:walk(x,p)
  scanned+=1
 except (ValueError,UnicodeError,OSError):pass
print('indexed files',scanned,'module suffixes',len(index),flush=True)
unique={m:next(iter(rs)) for m,rs in index.items() if len(rs)==1};resolved=dict(old['resolved'])
if (O/'EJS_recursive-history-resolution.json').exists():resolved.update(json.loads((O/'EJS_recursive-history-resolution.json').read_text())['found'])
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def blob(oid):
 proc.stdin.write((oid+'\n').encode());proc.stdin.flush();head=proc.stdout.readline().split();n=int(head[2]);b=proc.stdout.read(n);proc.stdout.read(1);return b
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
for ln in subprocess.check_output(['git','ls-tree','-r','HEAD'],text=True).splitlines():
 meta,p=ln.split('\t',1)
 if not p.endswith(('.lean','.lean.txt')):continue
 oid=meta.split()[2];b=blob(oid);h=hashlib.sha256(b).hexdigest()
 resolved.setdefault(h,dict(blob=oid,revision=revision,path=p,bytes=len(b)))
def imports(b):
 s=re.sub(r'/\-.*?\-/','',b.decode(),flags=re.S);s=re.sub(r'--[^\n]*','',s)
 return [m.replace('.','/') for ln in s.splitlines() if re.match(r'^\s*(?:public\s+|private\s+)?import\s',ln) for m in re.sub(r'^\s*(?:public\s+|private\s+)?import\s+','',ln).split() if re.fullmatch(r'[\w.]+',m)]
roots=sorted({m for r in state['progress']['pending'] for m in r['missing'] if m not in known});queue=list(roots);selected={};blocked={};prefixes={'Init','Lean','Std','Mathlib','Aeneas','AeneasMeta','Batteries','Qq','Cli','Lake','Plausible','Aesop','ImportGraph','ProofWidgets','LeanSearchClient'}
while queue:
 m=queue.pop()
 if m in known or m in selected or m in blocked or m.split('/')[0] in prefixes:continue
 if m in excluded:blocked[m]=dict(reason='original unresolved selected hash / excluded worker-owned module');continue
 if m not in index:blocked[m]=dict(reason='no source attestation');continue
 if m not in unique:blocked[m]=dict(reason='ambiguous source hashes',hashes=index[m]);continue
 h=unique[m]
 if h not in resolved:blocked[m]=dict(reason='attested hash not resolved by HEAD/retained index',sha256=h,attestation=index[m][h]);continue
 z=resolved[h];b=blob(z['blob']);assert hashlib.sha256(b).hexdigest()==h
 clean=re.sub(r'/\-.*?\-/','',b.decode(),flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
 if re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\s',clean,re.M):blocked[m]=dict(reason='forbidden proof token in historical source',sha256=h);continue
 ds=imports(b);selected[m]=dict(module=m,source_sha256=h,**z,imports=ds,attestation=index[m][h]);queue.extend(ds)
proc.terminate();out=dict(roots=roots,ready=list(selected.values()),blocked=blocked,attestation_files_indexed=scanned,policy='Only unique exact recorded source hashes; no proof editing; original unresolved selected hashes are excluded, never substituted.')
(O/'EJS_recursive-frontier.json').write_text(json.dumps(out,indent=2)+'\n');print('eligible recursive',len(selected),'blocked',len(blocked),flush=True)
