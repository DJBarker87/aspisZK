"""One scratch frozen Rust tree; no production source mutation."""
from pathlib import Path
import subprocess,json,tomllib,posixpath,hashlib,time,sys
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-s-compose-20261029';H='dombarker@100.108.41.90';REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def get(p):return subprocess.check_output(['git','show',REV+':'+p])
root=tomllib.loads(get('Cargo.toml').decode());seen=set();pending=list(root['workspace']['members']);dirs=[]
def tables(d):
 for k,v in d.items():
  if k in ('dependencies','dev-dependencies','build-dependencies') and isinstance(v,dict):yield v
  elif k=='target':
   for t in v.values():yield from tables(t)
while pending:
 p=posixpath.normpath(pending.pop());assert not p.startswith('../') and not p.startswith('/') and '*' not in p
 if p in seen:continue
 seen.add(p);doc=tomllib.loads(get(p+'/Cargo.toml').decode());dirs.append(p)
 for tab in tables(doc):
  for name,spec in tab.items():
   if not isinstance(spec,dict):continue
   if spec.get('workspace'):
    spec=root['workspace']['dependencies'][name];base='.'
   else:base=p
   if isinstance(spec,dict) and 'path' in spec:pending.append(posixpath.normpath(base+'/'+spec['path']))
paths=['Cargo.toml','Cargo.lock']+sorted(dirs)
tree=subprocess.check_output(['git','ls-tree','--name-only',REV],text=True).splitlines()
for p in ['rust-toolchain.toml','rust-toolchain','.cargo']:
 if p in tree:paths.append(p)
# Every admission precedes any source upload. Refusals never launch work.
for retry in range(11):
 code=f'''from pathlib import Path
import subprocess,json,sys
b=Path({B!r});log=b/'NED_RUST_SETUP-barrier.log'
with log.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NED_RUST_SETUP-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
print(log.read_text());sys.exit(r.returncode)
'''
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True);(E/f'NED_RUST_SETUP-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==255:
  if retry<10:time.sleep(60);continue
  raise SystemExit('transport exhausted')
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except Exception:
  if retry==0:time.sleep(30);continue
  raise SystemExit('STOP reservation JSON missing')
 if r.returncode==0 and ad.get('allowed') is True:break
 if r.returncode==78 or ad.get('allowed') is False:
  if retry<10:time.sleep(180);continue
 raise SystemExit('admission refused')
# Archive streamed without creating a second local source corpus.
archive=subprocess.Popen(['git','archive','--format=tar','--prefix=NED_src/',REV,*paths],stdout=subprocess.PIPE)
upload=subprocess.Popen(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'tar -x -C '+B],stdin=archive.stdout,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
archive.stdout.close();out,err=upload.communicate();arc=archive.wait()
(E/'NED_RUST_UPLOAD.log').write_bytes(out+err);assert arc==0 and upload.returncode==0,(arc,upload.returncode,err)
# Source content is pinned separately from this host path and dependency graph.
manifest={}
for line in subprocess.check_output(['git','ls-tree','-rl',REV,*paths],text=True).splitlines():
 meta,p=line.split('\t',1);manifest[p]=dict(git_blob=meta.split()[2],bytes=int(meta.split()[3]))
(E/'NED_RUST_SOURCE_PINS.json').write_text(json.dumps(dict(revision=REV,workspace=B+'/NED_src',paths=paths,files=manifest,admission=ad,lock_sha256=hashlib.sha256(get('Cargo.lock')).hexdigest()),indent=1)+'\n')
print('uploaded frozen scratch workspace:',len(manifest),'files in',len(dirs),'workspace/path crates')
