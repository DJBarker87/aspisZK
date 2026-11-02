from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
from html import unescape
import re,hashlib,json
base=Path('/home/dombarker/.kani/kani-0.67.0');tool=(base/'rust-toolchain-version').read_text();p=base/'toolchain/share/doc/rust/html/src/core/slice/specialize.rs.html';data=p.read_bytes();s=unescape(re.sub('<[^>]+>','',data.decode()));a=s.index('impl SpecFill<u8>');z=s.index('impl SpecFill<i8>',a);part=s[a:z]
assert 'crate::intrinsics::write_bytes(self.as_mut_ptr(), value, self.len());' in part
print(json.dumps(dict(toolchain=tool,path=str(p),sha256=hashlib.sha256(data).hexdigest(),snippet=part,classification='u8 fill specialization is native write_bytes intrinsic, not protocol-loop unwinding')))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr;(E/'NEM_STD_FILL.json').write_text(r.stdout)
