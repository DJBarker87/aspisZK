"""Read-only frozen ELF/sysroot inspection; no compiler or proof execution."""
from pathlib import Path
import subprocess,json,hashlib,re,time
E=Path(__file__).resolve().parent
HOST='dombarker@100.108.41.90'
REMOTE=r'''
from pathlib import Path
import subprocess,hashlib,json
root=Path('/home/dombarker/project-offloads/codex-pv-c474-20261029')
obj=Path('/home/dombarker/.cache/solana/v1.52/platform-tools/llvm/bin/llvm-objdump')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files={}; artifacts=[]
for flavor,name,expected in [('pool','aspis_pool.so','121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'),('default','aspis_r1_cost_probe_program.so','f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4'),('devnet','aspis_r1_cost_probe_program.so','63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299')]:
 elf=root/('elf-'+flavor)/name
 assert sha(elf)==expected
 artifacts.append(dict(flavor=flavor,path=str(elf),sha256=sha(elf),size=elf.stat().st_size))
 files['NFO_'+flavor+'_build_command.json']=(elf.parent/'command.json').read_text()
 if flavor=='pool':
  for flag,label in [('-d','disassembly'),('-R','relocations'),('-T','dynsym'),('-t','symbols')]:
   files['NFO_pool_'+label+'.txt']=subprocess.check_output([str(obj),flag,'--demangle',str(elf)],text=True)
files['NFO_INSPECTION_PINS.json']=json.dumps(dict(artifacts=artifacts,objdump=dict(path=str(obj),sha256=sha(obj)),classification='static ELF inspection; no compiler or native proof'),indent=2)+'\n'
print(json.dumps(files))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',HOST,'python3'],input=REMOTE,text=True,capture_output=True)
 if r.returncode!=255:break
 (E/'NFO_TRANSPORT.jsonl').open('a').write(json.dumps(dict(step='inspect',retry=retry,exit=255,stderr=r.stderr))+'\n')
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
for name,data in json.loads(r.stdout).items():
 p=E/name
 if 'disassembly' in name:
  import lzma
  (E/(name+'.xz')).write_bytes(lzma.compress(data.encode(),preset=6))
  (E/(name+'.sha256')).write_text(hashlib.sha256(data.encode()).hexdigest()+'\n')
 else:p.write_text(data)
print('Pinned all three release ELFs; captured Pool disassembly and symbols')
