"""Focused changed static dependency inventory; reuse prior runtime evidence."""
import hashlib,json,os,pathlib,resource,sys,tarfile,time,traceback
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));os.umask(0o077)
P=pathlib.Path;S=P('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024');B=S/'SbfClosure-20261025-v1';OLD=B/'analysis-v1';NEW=B/'analysis-v2';t=time.monotonic()
r=dict(print_axioms='N/A',command=['python3','-B','-c','literal SbfClosure_inventory_continue.py via SSH'])
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
try:
 assert S.resolve()==S and B.resolve()==B and os.getuid()==1000
 assert (S/'OWNER').read_text()=='SbfRecapturePrep 20261024\n' and (B/'OWNER').read_text()=='SbfClosure 20261025\n'
 pins={'source-inputs.json':'a84a528cfc4b294c603fe5381343cdaf9df0547467bcc94e61a67e5111adb9d1','src/Cargo.lock':'5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef','rustc-diagnostics.py':'fa74d69e097b6eab43809943614133081abb6beb19406018961402b86494ff84'}
 for path,h in pins.items():assert sha(S/path)==h
 cg=P('/sys/fs/cgroup');res=[]
 def visit(p):
  if p!=cg and 'populated 1' not in (p/'cgroup.events').read_text():return
  cap=(p/'memory.max').read_text().strip() if (p/'memory.max').exists() else 'max'
  if cap!='max':res.append((str(p),int(cap)));return
  for q in p.iterdir():
   if q.is_dir():visit(q)
 visit(cg);assert sum(x[1] for x in res)+536870912<55*1024**3
 r['reservations']=res;NEW.mkdir(mode=0o700);incoming=[]
 with tarfile.open(fileobj=sys.stdin.buffer,mode='r|') as tar:
  for m in tar:
   p=pathlib.PurePosixPath(m.name);assert not p.is_absolute() and '..' not in p.parts
   if m.isdir():continue
   assert m.isfile() and m.size<256000 and (m.name.startswith('tools/sbf-closure-20261025/SbfClosure_') or m.name=='evidence/sbf-closure-20261025/REVISION')
   dst=NEW/m.name;dst.parent.mkdir(parents=True,exist_ok=True)
   with tar.extractfile(m) as a,dst.open('xb') as b:b.write(a.read(256001))
   incoming.append(dict(path=m.name,sha256=sha(dst),bytes=dst.stat().st_size))
 sys.path.insert(0,str(NEW/'tools/sbf-closure-20261025'))
 import SbfClosure_receipt as receipt
 import SbfClosure_inventory as inv
 exports={x['path']:x for x in json.loads((OLD/'analysis.receipt.json').read_text())['exports']}
 def immutable(path):
  p=OLD/path;assert p.stat().st_size==exports[path]['bytes'] and sha(p)==exports[path]['sha256'],path
  return p.read_bytes()
 material=json.loads(immutable('evidence/sbf-recapture-prep-20261024/materialized-files.json'))
 manifest={x['path'].removeprefix('src/'):x for x in material}
 revision=(NEW/'evidence/sbf-closure-20261025/REVISION').read_bytes().strip()
 def gitview(*a):
  if a==('rev-parse','HEAD'):return revision+b'\n'
  if a[0]=='show':
   rev,path=a[1].split(':',1)
   if rev==inv.REV:return immutable(path)
   assert rev==inv.SRC and path in manifest,'not in frozen materialization: '+path
   p=S/'src'/path;assert p.resolve()==p and p.stat().st_size<=5_000_000
   b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==manifest[path]['sha256'],path;return b
  assert a[0]=='ls-tree' and a[1:3]==('-r','--name-only')
  names=list(exports) if a[3]==inv.REV else list(manifest)
  return ('\n'.join(sorted(p for p in names if any(p==q or p.startswith(q+'/') for q in a[4:])))+'\n').encode()
 receipt.git=gitview;inv.git=gitview
 r.update(helpers=incoming,source_revision=revision.decode(),exit=receipt.run('inventory.receipt.json',inv.main))
except Exception as e:r.update(exit=1,error=repr(e),traceback=traceback.format_exc())
u=resource.getrusage(0);r.update(wall_seconds=time.monotonic()-t,peak_rss_kib=u.ru_maxrss,swap=u.ru_nswap)
with (NEW/'continuation.receipt.json').open('x') as f:json.dump(r,f,sort_keys=True);f.write('\n')
print(json.dumps(r,sort_keys=True));sys.exit(r['exit'])
