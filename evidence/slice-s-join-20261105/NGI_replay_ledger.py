"""Run unchanged NFX builder with additive equality check in a private read sandbox.

Sparse inputs are read verbatim from HEAD, pinned once by SHA256. No validation
predicate, builder return value, historical Git command or theorem is replaced.
"""
from pathlib import Path
import sys,subprocess,json,lzma,hashlib,importlib.abc,importlib.util,io,time,resource,traceback
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];start=time.monotonic()
tracked=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],cwd=R,text=True).splitlines();paths=set(tracked);used={};raw_open=Path.open;raw_exists=Path.exists;raw_isfile=Path.is_file
byname={}
for p in tracked:
 if p.startswith('evidence/') and p.endswith('.py'):byname.setdefault(Path(p).name,[]).append(p)
def rel(p):
 try:return str(p.relative_to(R))
 except ValueError:return None
def get(p):
 q=rel(p)
 if raw_isfile(p):
  with raw_open(p,'rb') as f:return f.read()
 assert q in paths,('untracked sparse read',q)
 data=subprocess.check_output(['git','show','HEAD:'+q],cwd=R);h=hashlib.sha256(data).hexdigest();dest=E/'NGI_pinned_inputs'/h
 if not raw_exists(dest):
  dest.parent.mkdir(parents=True,exist_ok=True)
  with raw_open(dest,'wb') as f:f.write(data)
 used[q]=dict(sha256=h,bytes=len(data),snapshot=str(dest.relative_to(E)));return data
def opened(p,mode='r',*a,**kw):
 if any(c in mode for c in 'wax+') and p.is_relative_to(R) and not p.is_relative_to(E):
  dest=E/'NGI_replay_outputs'/p.relative_to(R);dest.parent.mkdir(parents=True,exist_ok=True);return raw_open(dest,mode,*a,**kw)
 if raw_exists(p):return raw_open(p,mode,*a,**kw)
 if rel(p) in paths:
  data=get(p);return io.BytesIO(data) if 'b' in mode else io.StringIO(data.decode('utf-8' if kw.get('encoding') in [None,'locale'] else kw['encoding']))
 return raw_open(p,mode,*a,**kw)
Path.open=opened
Path.exists=lambda p:raw_exists(p) or rel(p) in paths
Path.is_file=lambda p:raw_isfile(p) or rel(p) in paths
class Loader(importlib.abc.Loader):
 def __init__(self,path):self.path=path
 def create_module(self,spec):return None
 def exec_module(self,m):
  p=R/self.path;m.__file__=str(p);exec(compile(get(p),str(p),'exec'),m.__dict__)
class Finder(importlib.abc.MetaPathFinder):
 def find_spec(self,fullname,path=None,target=None):
  options=byname.get(fullname+'.py',[])
  if not options:return None
  assert len(options)==1,(fullname,options)
  return importlib.util.spec_from_loader(fullname,Loader(options[0]),origin=str(R/options[0]))
sys.meta_path.append(Finder())
for p in (R/'evidence').iterdir():
 if p.is_dir():sys.path.insert(0,str(p))
rc=0
try:
 import NFX_ledger
 d,_,_=NFX_ledger.build();baseline=json.loads(lzma.decompress((NFX_ledger.E/'NFX_LEDGER.json.xz').read_bytes()));d['NFX_source_revision']=baseline['NFX_source_revision'];assert d==baseline,'NFX baseline mismatch'
 result=dict(unchanged_builder=True,exact_baseline_equality=True,coverage=d['NFX_coverage'],scope='Historical 587-row NFX baseline only; corrected inventory basis is 599 and not overwritten')
except Exception:rc=1;result=dict(error=traceback.format_exc());traceback.print_exc()
u=resource.getrusage(resource.RUSAGE_SELF)
receipt=dict(target='unchanged NFX_ledger.build + exact baseline equality',exit_status=rc,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swaps=u.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),print_axioms='N/A Python; no prover launch',result=result,sparse_inputs=used)
(E/'NGI_REPLAY_NFX_LEDGER.json').write_text(json.dumps(receipt,indent=1)+'\n');print(json.dumps(dict(exit=rc,result=result,sparse_inputs=len(used))));sys.exit(rc)
