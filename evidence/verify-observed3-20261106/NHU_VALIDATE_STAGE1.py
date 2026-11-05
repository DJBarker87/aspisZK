"""Execute the original stage1 admission unchanged against its immutable Git snapshot."""
from pathlib import Path
import subprocess,runpy,json,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1]
class Pinned:
 def __init__(self,path,revision):self.path=path;self.revision=revision
 def __truediv__(self,name):return Pinned(self.path/name,self.revision)
 def read_bytes(self):return subprocess.check_output(['git','show',self.revision+':'+str(self.path)],cwd=R)
 def read_text(self):return self.read_bytes().decode()
def validate():
 seal=json.loads((E/'NHU_STAGE1_SEAL.json').read_text());revision=seal['revision'];relative=E.relative_to(R)
 for name,sha in seal['files'].items():assert hashlib.sha256(Pinned(relative/name,revision).read_bytes()).hexdigest()==sha,name
 assert hashlib.sha256((E/'NHU_validate.py').read_bytes()).hexdigest()==seal['files']['NHU_validate.py']
 ns=runpy.run_path(str(E/'NHU_validate.py'));fn=ns['validate'];fn.__globals__['E']=Pinned(relative,revision)
 out=fn();assert out['status']=='PASS' and out['new_rows']==['TX1:130'];return out
if __name__=='__main__':print(json.dumps(validate()))
