from pathlib import Path
import json,lzma,subprocess,hashlib,re
D=Path(__file__).resolve().parent;old=json.load(lzma.open(D.parent/'pv-mfb-20261029/exact-traces.json.xz'));tree={s.split('\t')[1]:s.split('\t')[0].split()[-1] for s in subprocess.check_output(['git','ls-tree','-r','HEAD'],text=True).splitlines()};cache={};proc=subprocess.Popen(["git","cat-file","--batch"],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def raw(p):
 if p not in cache:
  proc.stdin.write((tree[p]+'\n').encode());proc.stdin.flush();h=proc.stdout.readline().split();cache[p]=proc.stdout.read(int(h[2]));proc.stdout.read(1)
 return cache[p]
def imports(b):
 s=b.decode();s=re.sub(r'/\-.*?\-/','',s,flags=re.S);s=re.sub(r'--[^\n]*','',s);return re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)',s,re.M)
ej=json.loads(raw('evidence/envj-rebuild-20261026/EJR_final-inventory.json'));auth={x['module'].replace('/','.'):x for x in ej['selected'] if x.get('workspace')=='joint' and x.get('resolution')};ext={x['module'].replace('/','.') for x in json.load(open(D.parent/'pv-mfb-20261029/external-object-manifest.json'))};mods={k:v for r in old for k,v in r['modules'].items()};corrections=[]
for m,x in auth.items():
 p=x['resolution']['path']
 if p not in tree:continue
 b=raw(p);h=hashlib.sha256(b).hexdigest()
 if h!=x['sha256']:continue
 if m in mods and mods[m]['sha256']!=h:corrections.append(dict(module=m,old=mods[m],joint_authority=x))
 mods[m]=dict(path=p,blob=tree[p],sha256=h,imports=imports(b),authority='EJR joint')
p='docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineV2.lean';b=raw(p);mods['R1Z.PrivacyR1HeadlineV2']=dict(path=p,blob=tree[p],sha256=hashlib.sha256(b).hexdigest(),imports=imports(b),authority='h5-double-prime')
results=[]
for r in old:
 seen={};gap=[]
 def visit(m,chain):
  if m in seen or m in ext:return
  if m not in mods:gap.append(dict(module=m,chain=chain));return
  v=mods[m];seen[m]=dict(v,chain=chain+[m])
  for dep in v['imports']:visit(dep,chain+[m])
 for root in ([r['closing']['module']] if r['closing'] else [])+r['audit_roots']:visit(root,[])
 results.append(dict(id=r['id'],closing=r['closing'],audit_roots=r['audit_roots'],modules=seen,gaps=gap))
(D/'authority-corrections.json').write_text(json.dumps(corrections,indent=2)+'\n');(D/'resolved-traces.json.xz').write_bytes(lzma.compress(json.dumps(results,indent=2).encode()))
print('corrections',[(x['module']) for x in corrections]);print([(r['id'],len(r['modules']),len(r['gaps'])) for r in results if r['gaps']])
