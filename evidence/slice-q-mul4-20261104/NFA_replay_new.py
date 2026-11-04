from pathlib import Path
import json,lzma,hashlib,base64,subprocess,os,sys,time,resource,importlib,shutil
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent;S=E/'NFA_peer_scratch'
meta=json.loads((E/'NFA_NEW_PROVENANCE.json').read_text());compressed=(E/'NFA_NEW_ARCHIVE.json.xz').read_bytes()
assert hashlib.sha256(compressed).hexdigest()==meta['compressed_sha256']
raw=lzma.decompress(compressed);assert hashlib.sha256(raw).hexdigest()==meta['raw_sha256'];pack=json.loads(raw)
assert pack['revision']==meta['revision'];S.mkdir(exist_ok=True)
for name,item in pack['files'].items():
 b=pack['blobs'][item['blob']];raw=b['content'].encode() if b['encoding']=='utf8' else base64.b64decode(b['content']);assert hashlib.sha256(raw).hexdigest()==b['sha256']
 p=S/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
# Private Python module locations keep every relative evidence read in this
# deduplicated view; static artifacts are read-only links to this worktree.
pyfiles={Path(x) for x in subprocess.check_output(['git','ls-files','*.py'],cwd=R,text=True).splitlines() if x.startswith('evidence/') and (R/x).is_file()}
parents={p for f in pyfiles for p in f.parents}
def mirror(src,dst,rel):
 dst.mkdir(exist_ok=True)
 for child in src.iterdir():
  if child==E or child.name=='slice-q-compose4-20261104':continue
  cr=rel/child.name;target=dst/child.name
  if child.is_dir() and cr in parents:mirror(child,target,cr)
  elif child.is_file() and cr in pyfiles:
   if not target.exists():target.write_bytes(child.read_bytes())
  elif not target.exists():target.symlink_to(child,target_is_directory=child.is_dir())
mirror(R/'evidence',S/'evidence',Path('evidence'))
for top in ['design','docs','lean']:
 if (R/top).exists() and not (S/top).exists():(S/top).symlink_to(R/top,target_is_directory=True)
os.environ['GIT_DIR']=subprocess.check_output(['git','rev-parse','--absolute-git-dir'],cwd=R,text=True).strip();os.environ['GIT_WORK_TREE']=str(S)
old_text=Path.write_text;old_bytes=Path.write_bytes;writes=[]
def guard(p):
 assert Path(p).resolve().is_relative_to(S),('forbidden write',str(p));writes.append(str(Path(p).relative_to(S)))
def wt(p,*a,**k):guard(p);return old_text(p,*a,**k)
def wb(p,*a,**k):guard(p);return old_bytes(p,*a,**k)
Path.write_text=wt;Path.write_bytes=wb
P=S/'evidence/slice-q-compose4-20261104';sys.path.insert(0,str(P));start=time.monotonic();rc=1;error=None;result=None
try:
 result=importlib.import_module('NEW_validate').validate();rc=0
except Exception as ex:error=repr(ex)
finally:
 use=resource.getrusage(resource.RUSAGE_SELF)
 report=dict(revision=meta['revision'],target='unchanged NEW_validate.validate including inherited replay',exit_status=rc,wall_seconds=time.monotonic()-start,peak_rss_kib=int(use.ru_maxrss/1024),swaps=use.ru_nswap,error=error,result=result,writes=writes,print_axioms='Inherited standard-only proof receipts checked by validator; no prover launched')
 old_text(E/'NFA_NEW_REPLAY.json',json.dumps(report,indent=2)+'\n')
print(json.dumps(report));sys.exit(rc)
