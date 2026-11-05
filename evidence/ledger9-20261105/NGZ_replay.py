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
 data=subprocess.check_output(['git','show','HEAD:'+q],cwd=R);h=hashlib.sha256(data).hexdigest();dest=E/'NGZ_pinned_inputs'/h
 if not raw_exists(dest):
  dest.parent.mkdir(parents=True,exist_ok=True)
  with raw_open(dest,'wb') as f:f.write(data)
 used[q]=dict(sha256=h,bytes=len(data),snapshot=str(dest.relative_to(E)));return data
def opened(p,mode='r',*a,**kw):
 if any(c in mode for c in 'wax+') and p.is_relative_to(R) and not p.is_relative_to(E):
  dest=E/'NGZ_replay_outputs'/p.relative_to(R);dest.parent.mkdir(parents=True,exist_ok=True);return raw_open(dest,mode,*a,**kw)
 if not raw_exists(p) and raw_isfile(Path(str(p)+'.xz')):
  raw=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==Path(str(p)+'.sha256').read_text().strip()
  return io.BytesIO(raw) if 'b' in mode else io.StringIO(raw.decode())
 if raw_exists(p):return raw_open(p,mode,*a,**kw)
 if rel(p) in paths:
  data=get(p);return io.BytesIO(data) if 'b' in mode else io.StringIO(data.decode('utf-8' if kw.get('encoding') in [None,'locale'] else kw['encoding']))
 return raw_open(p,mode,*a,**kw)
import builtins
raw_builtin_open=builtins.open
def builtin_open(file,mode='r',*a,**kw):
 if isinstance(file,(str,Path)):
  p=Path(file)
  if not raw_exists(p) and rel(p) in paths:
   data=get(p);return io.BytesIO(data) if 'b' in mode else io.StringIO(data.decode())
 return raw_builtin_open(file,mode,*a,**kw)
builtins.open=builtin_open
Path.open=opened
Path.exists=lambda p:raw_exists(p) or rel(p) in paths
Path.is_file=lambda p:raw_isfile(p) or rel(p) in paths

# Sparse glob inventory is derived from committed tree names, never candidate outcomes.
import fnmatch
raw_glob=Path.glob
by_evidence={}
for q in tracked:
 parts=q.split('/')
 if len(parts)>2:by_evidence.setdefault('/'.join(parts[:2]),[]).append(q)
def sparse_glob(p,pattern,*a,**kw):
 found=set(raw_glob(p,pattern,*a,**kw));base=rel(p)
 if base:
  options=by_evidence.get('/'.join(base.split('/')[:2]),[])
  bits=pattern.split('/')
  for q in options:
   if not q.startswith(base+'/'):continue
   tail=q[len(base)+1:];parts=tail.split('/')
   if len(parts)==len(bits) and all(fnmatch.fnmatchcase(x,y)for x,y in zip(parts,bits)):found.add(R/q)
 return iter(sorted(found))
Path.glob=sparse_glob

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
import importlib.machinery
raw_loader_data=importlib.machinery.SourceFileLoader.get_data
def loader_data(self,path):
 p=Path(path)
 if not raw_isfile(p) and rel(p) in paths:return get(p)
 return raw_loader_data(self,path)
importlib.machinery.SourceFileLoader.get_data=loader_data
for p in (R/'evidence').iterdir():
 if p.is_dir():sys.path.insert(0,str(p))
task=sys.argv[1];rc=0
jobs={
'NFX':'evidence/ledger7-20261104/NFX_ledger.py',
'NGB':'evidence/inv-repair-20261104/NGB_validate.py',
'NFT':'evidence/slice-d-field-20261104/NFT_certify.py',
'NFU':'evidence/slice-d-check-20261104/NFU_certify.py',
'NFY':'evidence/slice-s-retarget-20261104/NFY_finalize.py',
'NGE':'evidence/slice-s-retarget2-20261104/NGE_finalize.py',
'NGF':'evidence/slice-s-retarget3-20261104/NGF_finalize.py',
'NGI':'evidence/slice-s-join-20261105/NGI_finalize.py',
'NFV':'evidence/pool-retdata3-20261104/NFV_validate.py',
'NGH':'evidence/slice-d-field3-20261105/NGH_certify.py','NGD':'evidence/slice-d-parser-20261104/NGD_validate.py','NFW':'evidence/slice-d-prepare-20261104/NFW_certify.py','NGC':'evidence/slice-d-checkpoint-20261104/NGC_certify.py','NGO':'evidence/slice-d-parser2-20261105/NGO_validate.py','NGM':'evidence/slice-d-finish-20261105/NGM_validate.py','NGT':'evidence/transcript-scalars-20261105/NGT_validate.py','NGV':'evidence/slice-d-parser3-20261105/NGV_validate.py','NGN':'evidence/slice-d-prepared-20261105/NGN_finalize.py','NGU':'evidence/prepared-claim-20261105/NGU_validate.py','NGK':'evidence/pool-retarget-20261105/NGK_validate.py','NGP':'evidence/exp-premises-20261105/NGP_validate.py','NGR':'evidence/history-persist-20261105/NGR_validate.py','NGS':'evidence/carriers-bind-20261105/NGS_validate.py','NGA':'evidence/slice-d-field2-20261104/NGA_certify.py','NGG':'evidence/pool-prefix-20261105/NGG_validate.py'}
try:
 path=R/jobs[task];namespace={'__file__':str(path),'__name__':'__main__'}
 if task=='NFX':
  namespace['__name__']='NGZ_NFX';exec(compile(get(path),str(path),'exec'),namespace)
  d,_,_=namespace['build']();old=json.loads(lzma.decompress(get(path.parent/'NFX_LEDGER.json.xz')));d['NFX_source_revision']=old['NFX_source_revision'];assert d==old
 else:
  sys.argv=[str(path)]+(['wide',json.loads(get(path.parent/'NGH_AUDIT.json'))['review']] if task=='NGH' else [])
  exec(compile(get(path),str(path),'exec'),namespace)
 result={'unchanged_validator':jobs[task],'result':'PASS'}
except Exception:rc=1;result={'error':traceback.format_exc()};traceback.print_exc()
u=resource.getrusage(resource.RUSAGE_SELF)
receipt=dict(target=task,exit_status=rc,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swaps=u.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),print_axioms='N/A Python; no prover launch',result=result,sparse_inputs=used)
(E/('NGZ_REPLAY_'+task+'.json')).write_text(json.dumps(receipt,indent=1)+'\n');print(json.dumps(dict(exit=rc,result=result,sparse_inputs=len(used))));sys.exit(rc)
