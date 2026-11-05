"""Load sparse historical validator modules verbatim from committed Git blobs."""
from pathlib import Path
import importlib.abc,importlib.util,subprocess,hashlib,json,sys
E=Path(__file__).resolve().parent;R=E.parents[1];used={}
paths=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],cwd=R,text=True).splitlines()
class Loader(importlib.abc.Loader):
 def __init__(self,p):self.p=p
 def create_module(self,spec):return None
 def exec_module(self,m):
  raw=subprocess.check_output(['git','show','HEAD:'+self.p],cwd=R);m.__file__=str(R/self.p)
  used[self.p]=dict(sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),source='unchanged committed Git blob')
  exec(compile(raw,m.__file__,'exec'),m.__dict__)
  (E/'NHP_SPARSE_IMPORTS.json').write_text(json.dumps(used,indent=1)+'\n')
class Finder(importlib.abc.MetaPathFinder):
 def find_spec(self,fullname,path=None,target=None):
  name=fullname+'.py';candidates=[p for p in paths if p.startswith('evidence/') and p.endswith('/'+name) and '/sources/' not in p and '/diagnostics/' not in p]
  if not candidates:return None
  shortest=min(len(Path(p).parts) for p in candidates);candidates=[p for p in candidates if len(Path(p).parts)==shortest]
  assert len(candidates)==1,(fullname,candidates)
  return importlib.util.spec_from_loader(fullname,Loader(candidates[0]),origin=str(R/candidates[0]))
if not any(type(f).__name__=='Finder' and type(f).__module__==__name__ for f in sys.meta_path):sys.meta_path.append(Finder())
# Missing sparse data is a read-only projection of the exact committed bytes.
# Existing files and every write retain the ordinary filesystem implementation.
import io
_raw_open=Path.open;_raw_exists=Path.exists;_raw_isfile=Path.is_file
tracked=set(paths)
def relative(p):
 try:return str(p.absolute().relative_to(R))
 except ValueError:return None
def sparse_open(p,mode='r',*args,**kwargs):
 rel=relative(p)
 if not any(c in mode for c in 'wax+') and not _raw_exists(p) and rel in tracked and not p.absolute().is_relative_to(E):
  raw=subprocess.check_output(['git','show','HEAD:'+rel],cwd=R)
  used[rel]=dict(sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),source='unchanged committed Git data blob')
  with _raw_open(E/'NHP_SPARSE_IMPORTS.json','w') as f:f.write(json.dumps(used,indent=1)+'\n')
  return io.BytesIO(raw) if 'b' in mode else io.StringIO(raw.decode(kwargs.get('encoding') or 'utf-8'))
 return _raw_open(p,mode,*args,**kwargs)
Path.open=sparse_open
