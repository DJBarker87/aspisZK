"""Private dry replay: resolve module names using EJR/EJS authority, pin research bytes."""
import subprocess,json,pathlib,hashlib,re,csv
P=pathlib.Path(__file__).parent; REV=(P/'research-revision.txt').read_text().strip()
def git(path):return subprocess.check_output(['git','show',REV+':'+path],stderr=subprocess.DEVNULL)
def js(path):return json.loads(git(path))
def sha(x):return hashlib.sha256(x).hexdigest()
files=subprocess.check_output(['git','ls-tree','-r','--name-only',REV],text=True).splitlines(); exists=set(files)
inv=js('evidence/envj-rebuild-20261026/EJR_final-inventory.json'); authority={}
for r in inv['selected']:
 if r.get('workspace')=='joint' and r.get('resolution'):authority[r['module']]={**r['resolution'],'authority':'EJR_final-inventory.json','historical_sha256':r['sha256']}
# The rebuild2 additions only resolve names not already selected by EJR.
records=['evidence/envj-rebuild-20261026/EJR_all-restored-sources.json']+[f for f in files if f.startswith('evidence/envj-rebuild2-20261026/') and (f.endswith('-payload.json') or f.endswith('/EJS_recursive-frontier.json'))]
for f in records:
 d=js(f); rows=d if isinstance(d,list) else d.get('rows',[])
 for r in rows:
  if r.get('workspace','joint') not in ['joint','EJS_missing']:continue
  m=r.get('module');res=r.get('resolution') or r
  if m and res.get('path') and m not in authority:authority[m]={**res,'authority':f}
def uncomment(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;i+=2
  elif not depth and s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j
  else:
   if not depth:out.append(s[i])
   elif s[i]=='\n':out.append('\n')
   i+=1
 return ''.join(out)
def imports(s):
 out=[]
 for l in uncomment(s).splitlines():
  z=re.match(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(.*)$',l)
  if z:out.extend(n.replace('.','/') for n in z[1].split() if n not in ['all'])
 return out
nodes={};external=set();order=[];busy=set();unresolved=[]
def visit(m):
 if m in nodes or m in external:return
 assert m not in busy,('cycle',m)
 r=authority.get(m)
 if not r:
  # New privacy modules have a canonical namespace path; never choose a grep hit.
  path='docs/research/v8-r0-zk-20261009/lean/'+m+'.lean'
  if path in exists:r={'path':path,'authority':'canonical privacy namespace, not in rebuild selection'}
  elif m.startswith(('Mathlib/','Aeneas/','Batteries/','Lean/','Std/','Init/','Qq/','Aesop/','Plausible/','ImportGraph/','ProofWidgets/','LeanSearchClient/','Cli/')) or m in ['Mathlib','Aeneas','Batteries','Lean','Std','Init','Qq','Aesop']:external.add(m);return
  else:unresolved.append(m);return
 path=r['path']
 try:b=git(path)
 except subprocess.CalledProcessError:unresolved.append({'module':m,'missing_research_path':path,'resolution':r});return
 s=b.decode();busy.add(m);deps=imports(s)
 for d in deps:visit(d)
 busy.remove(m)
 n={'module':m,'source_path':path,'source_sha256':sha(b),'resolution':r,'imports':deps}
 n['deps_fingerprint']=sha(json.dumps([(d,nodes[d]['source_sha256'],nodes[d]['deps_fingerprint']) if d in nodes else (d,'pinned external' if d in external else 'UNRESOLVED') for d in deps],separators=(',',':')).encode())
 nodes[m]=n;order.append(m)
 # Source staging is temporary; never committed.
 dst=P/'staged-sources'/(m+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(b)
roots=['R1Z/PrivacyR1HeadlineDeployedReal','R1Z/PrivacyR1HeadlineV2']
for m in roots:visit(m)
plan={'revision':REV,'roots':roots,'project_count':len(order),'direct_external_boundary':sorted(external),'unresolved':unresolved,'order':order,'nodes':nodes,'fingerprint_rule':'recursive source/import fingerprint; runtime object fingerprint recorded separately per compile/reuse'}
(P/'replay-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
with (P/'replay-plan.tsv').open('w') as f:
 w=csv.writer(f,delimiter='\t');w.writerow(['order','module','source path','source sha256','deps fingerprint'])
 for i,m in enumerate(order,1):n=nodes[m];w.writerow([i,m.replace('/','.'),n['source_path'],n['source_sha256'],n['deps_fingerprint']])
print(json.dumps({k:v for k,v in plan.items() if k not in ['nodes','order']},indent=2))
