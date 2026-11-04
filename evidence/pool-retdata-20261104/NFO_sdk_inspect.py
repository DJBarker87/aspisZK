from pathlib import Path
import subprocess,json,hashlib,lzma,re
E=Path(__file__).resolve().parent
code=r'''from pathlib import Path
import json,hashlib
files={};pins=[]
for p in Path('/home/dombarker/.cargo/registry/src').glob('*/solana-cpi-2.2.1/src/lib.rs'):
 raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest();pins.append(dict(path=str(p),sha256=h,size=len(raw)))
 files[h]=raw.decode()
assert len(files)==1, pins
print(json.dumps(dict(pins=pins,source=next(iter(files.values())))))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'NFO_solana_cpi_2_2_1.rs.txt').write_text(out.pop('source'))
(E/'NFO_SDK_PINS.json').write_text(json.dumps(out,indent=1)+'\n')
# Extend the pinned ELF window once to include the Some and None stores.
raw=lzma.decompress((E/'NFO_pool_disassembly.txt.xz').read_bytes()).decode();ls=raw.splitlines()
window='\n'.join(l for l in ls if (m:=re.match(r'\s*([0-9a-f]+):',l)) and 0x61028<=int(m[1],16)<0x61208)+'\n'
(E/'NFO_get_sdk_complete_window.txt').write_text(window)
print('Pinned identical SDK source candidates and complete get-return wrapper')
