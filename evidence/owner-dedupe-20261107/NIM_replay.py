"""Run unchanged NFX builder with additive equality check in a private read sandbox.

Sparse inputs are read verbatim from HEAD, pinned once by SHA256. No validation
predicate, builder return value, historical Git command or theorem is replaced.
"""
from pathlib import Path
import sys,subprocess,json,lzma,hashlib,importlib.abc,importlib.util,io,time,resource,traceback
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];start=time.monotonic()
tracked=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],cwd=R,text=True).splitlines();paths=set(tracked);used={};raw_open=Path.open;raw_exists=Path.exists;raw_isfile=Path.is_file
prior_inputs={}
for rp in E.glob('NIM_REPLAY_*.json'):
 prior_inputs.update(json.loads(rp.read_text()).get('sparse_inputs',{}))
byname={}
for p in tracked:
 if p.startswith('evidence/') and p.endswith('.py'):byname.setdefault(Path(p).name,[]).append(p)
def rel(p):
 try:return str(p.relative_to(R))
 except ValueError:return None
def get(p):
 q=rel(p)
 ref=Path(str(p)+'.REFERENCE.json')
 if raw_isfile(ref):
  x=json.loads(ref.read_text());key=x.get('stored_once',x.get('compressed'));z=ref.parent/key
  # packed refs use evidence-directory-relative paths
  if not raw_isfile(z):z=next(parent/key for parent in ref.parents if raw_isfile(parent/key))
  data=z.read_bytes();data=lzma.decompress(data) if x.get('encoding')=='xz' or 'compressed'in x else data
  assert hashlib.sha256(data).hexdigest()==x['sha256'];return data
 if q in used:
  with raw_open(E/used[q]['snapshot'],'rb')as f:return f.read()
 if q in prior_inputs:
  x=prior_inputs[q]
  with raw_open(E/x['snapshot'],'rb')as f:data=f.read()
  assert hashlib.sha256(data).hexdigest()==x['sha256'];used[q]=x;return data
 if raw_isfile(p):
  with raw_open(p,'rb') as f:return f.read()
 assert q in paths,('untracked sparse read',q)
 data=subprocess.check_output(['git','show','HEAD:'+q],cwd=R);h=hashlib.sha256(data).hexdigest();dest=E/'NIM_pinned_inputs'/h
 if not raw_exists(dest):
  dest.parent.mkdir(parents=True,exist_ok=True)
  with raw_open(dest,'wb') as f:f.write(data)
 used[q]=dict(sha256=h,bytes=len(data),snapshot=str(dest.relative_to(E)));return data
def opened(p,mode='r',*a,**kw):
 if not any(c in mode for c in 'wax+') and p.is_relative_to(R) and not p.is_relative_to(E):
  mirror=E/'NIM_replay_outputs'/p.relative_to(R)
  if raw_isfile(mirror):return raw_open(mirror,mode,*a,**kw)
 if any(c in mode for c in 'wax+') and p.is_relative_to(R) and not p.is_relative_to(E):
  dest=E/'NIM_replay_outputs'/p.relative_to(R);dest.parent.mkdir(parents=True,exist_ok=True);return raw_open(dest,mode,*a,**kw)
 if not raw_exists(p) and (raw_isfile(Path(str(p)+'.xz')) or rel(Path(str(p)+'.xz')) in paths):
  raw=lzma.decompress(get(Path(str(p)+'.xz')));assert hashlib.sha256(raw).hexdigest()==get(Path(str(p)+'.sha256')).decode().strip()
  return io.BytesIO(raw) if 'b' in mode else io.StringIO(raw.decode())
 if not raw_exists(p) and raw_isfile(Path(str(p)+'.REFERENCE.json')):
  data=get(p);return io.BytesIO(data) if 'b' in mode else io.StringIO(data.decode())
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
Path.exists=lambda p:raw_exists(p) or raw_isfile(Path(str(p)+'.REFERENCE.json')) or rel(p) in paths
Path.is_file=lambda p:raw_isfile(p) or raw_isfile(Path(str(p)+'.REFERENCE.json')) or rel(p) in paths

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

raw_run=subprocess.run
nested=[]
def sandbox_run(args,*a,**kw):
 if isinstance(args,list) and len(args)>1 and str(args[0])==sys.executable and str(args[1]).endswith('.py'):
  p=Path(args[1]);assert p.is_relative_to(R),('external validator process',args)
  oldargv=sys.argv;sys.argv=list(map(str,args[1:]));buf=io.StringIO();rc=0
  import contextlib
  try:
   with contextlib.redirect_stdout(buf),contextlib.redirect_stderr(buf):
    exec(compile(get(p),str(p),'exec'),{'__file__':str(p),'__name__':'__main__'})
  except SystemExit as e:rc=e.code or 0
  finally:sys.argv=oldargv
  nested.append(dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(get(p)).hexdigest(),exit=rc))
  out=buf.getvalue();result=subprocess.CompletedProcess(args,rc,out if kw.get('text') else out.encode(),'' if kw.get('text') else b'')
  if kw.get('check') and rc:raise subprocess.CalledProcessError(rc,args,output=result.stdout)
  return result
 return raw_run(args,*a,**kw)
subprocess.run=sandbox_run

raw_unlink=Path.unlink
raw_rmdir=Path.rmdir
def sandbox_unlink(p,*a,**kw):
 if p.is_relative_to(R) and not p.is_relative_to(E):
  dest=E/'NIM_replay_outputs'/p.relative_to(R)
  if raw_exists(dest):return raw_unlink(dest,*a,**kw)
  return None
 return raw_unlink(p,*a,**kw)
def sandbox_rmdir(p,*a,**kw):
 if p.is_relative_to(R) and not p.is_relative_to(E):
  dest=E/'NIM_replay_outputs'/p.relative_to(R)
  if raw_exists(dest):return raw_rmdir(dest,*a,**kw)
  return None
 return raw_rmdir(p,*a,**kw)
Path.unlink=sandbox_unlink
Path.rmdir=sandbox_rmdir
task=sys.argv[1];rc=0
jobs={'NHY': 'evidence/slice-d-entry4-20261106/NHY_certify.py', 'NHK': 'evidence/transcript-queries3-20261106/NHK_validate.py', 'NHN': 'evidence/q-leftovers-20261106/NHN_validate.py', 'NHG': 'evidence/verify-observed2-20261106/NHG_final_validate.py', 'NHS': 'evidence/prepared-close-20261106/NHS_certify.py', 'NHM': 'evidence/slice-d-pair2-20261106/NHM_validate.py', 'NHJ': 'evidence/slice-d-entry3-20261106/NHJ_certify.py', 'NHX': 'evidence/slice-d-pair3-20261106/NHX_validate.py', 'NHU': 'evidence/verify-observed3-20261106/NHU_validate2.py', 'NHP': 'evidence/pool-b3-20261106/NHP_validate.py'}
try:
 path=R/jobs[task];namespace={'__file__':str(path),'__name__':'__main__'}
 if task=='NFX':
  namespace['__name__']='NIM_NFX';exec(compile(get(path),str(path),'exec'),namespace)
  d,_,_=namespace['build']();old=json.loads(lzma.decompress(get(path.parent/'NFX_LEDGER.json.xz')));d['NFX_source_revision']=old['NFX_source_revision'];assert d==old
 else:
  sys.argv=[str(path)]+[]
  exec(compile(get(path),str(path),'exec'),namespace)
 result={'unchanged_validator':jobs[task],'result':'PASS'}
except Exception:rc=1;result={'error':traceback.format_exc()};traceback.print_exc()
u=resource.getrusage(resource.RUSAGE_SELF)
receipt=dict(target=task,exit_status=rc,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swaps=u.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),print_axioms='N/A Python; no prover launch',result=result,nested_validators=nested,sparse_inputs=used)
(E/('NIM_REPLAY_'+task+'.json')).write_text(json.dumps(receipt,indent=1)+'\n');print(json.dumps(dict(exit=rc,result=result,sparse_inputs=len(used))));sys.exit(rc)
