"""Read-only frozen ELF/sysroot inspection; no compiler or proof execution."""
from pathlib import Path
import subprocess,json,hashlib,re,time
E=Path(__file__).resolve().parent
HOST='dombarker@100.108.41.90'
REMOTE=r'''
from pathlib import Path
import subprocess,hashlib,json,re
root=Path('/home/dombarker/project-offloads/codex-pv-c474-20261029')
obj=Path('/home/dombarker/.cache/solana/v1.52/platform-tools/llvm/bin/llvm-objdump')
sysroot=Path('/home/dombarker/.rustup/toolchains/1.89.0-sbpf-solana-v1.52/lib/rustlib/src/rust/library')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files={};artifacts=[]
for flavor,expected in [('default','f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4'),('devnet','63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299')]:
 elf=root/('elf-'+flavor)/'aspis_r1_cost_probe_program.so';assert sha(elf)==expected
 dis=subprocess.check_output([str(obj),'-d',str(elf)],text=True)
 rel=subprocess.check_output([str(obj),'-R',str(elf)],text=True)
 dyn=subprocess.check_output([str(obj),'-T',str(elf)],text=True)
 files['NFH_'+flavor+'_disassembly.txt']=dis
 files['NFH_'+flavor+'_relocations.txt']=rel
 files['NFH_'+flavor+'_dynsym.txt']=dyn
 files['NFH_'+flavor+'_build_command.json']=(elf.parent/'command.json').read_text()
 lines=dis.splitlines();windows=[]
 for i,l in enumerate(lines):
  if re.search(r'\bmov64 r3, 0x2b0$',l):
   window='\n'.join(lines[max(0,i-8):i+12]);windows.append(window)
 files['NFH_'+flavor+'_688_windows.txt']='\n\n'.join(windows)+'\n'
 matches=re.findall(r'^([0-9a-f]+) R_SBF_64_32\s+sol_memcmp_\s*$',rel,re.M);assert len(matches)==1,matches
 addr=int(matches[0],16)
 wrapper=subprocess.check_output([str(obj),'-d','--start-address='+hex(addr-24),'--stop-address='+hex(addr+40),str(elf)],text=True)
 files['NFH_'+flavor+'_memcmp_wrapper.txt']=wrapper
 artifacts.append(dict(flavor=flavor,path=str(elf),sha256=sha(elf),size=elf.stat().st_size,syscall_symbol='sol_memcmp_',syscall_instruction=hex(addr),wrapper_entry=hex(addr-24),undefined=True,wrapper_instructions=wrapper))
for name,rel in [('NFH_core_slice_cmp.rs.txt','core/src/slice/cmp.rs'),('NFH_compiler_builtins_mem.rs.txt','compiler-builtins/compiler-builtins/src/mem/mod.rs')]:
 p=sysroot/rel;files[name]=p.read_text();artifacts.append(dict(path=str(p),sha256=sha(p),size=p.stat().st_size))
files['NFH_INSPECTION.json']=json.dumps(dict(artifacts=artifacts,objdump=dict(path=str(obj),sha256=sha(obj)),classification='static ELF/sysroot inspection; not native proof, no new trust adopted'),indent=2)+'\n'
print(json.dumps(files))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',HOST,'python3'],input=REMOTE,text=True,capture_output=True)
 if r.returncode!=255:break
 (E/'NFH_TRANSPORT.jsonl').open('a').write(json.dumps(dict(step='inspect',retry=retry,exit=255,stderr=r.stderr))+'\n')
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
for name,data in json.loads(r.stdout).items():
 p=E/name
 if 'disassembly' in name:
  import lzma
  (E/(name+'.xz')).write_bytes(lzma.compress(data.encode(),preset=6))
  (E/(name+'.sha256')).write_text(hashlib.sha256(data.encode()).hexdigest()+'\n')
 else:p.write_text(data)
print('Pinned two exact release ELFs, wrapper relocations,688-byte call windows and sysroot sources')
