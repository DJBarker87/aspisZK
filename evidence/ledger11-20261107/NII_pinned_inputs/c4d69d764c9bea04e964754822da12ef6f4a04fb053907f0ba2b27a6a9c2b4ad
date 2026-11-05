"""Read-only default ELF slot inventory. It does not manufacture source association."""
from pathlib import Path
import struct,json,hashlib,subprocess
B=Path(__file__).resolve().parent
p=Path('/home/dombarker/project-offloads/codex-cx-native-elfscope-20261028/NCR_B003/artifacts/aspis_r1_cost_probe_program.so')
b=p.read_bytes();h=hashlib.sha256(b).hexdigest();assert h=='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4'
assert b[:6]==b'\x7fELF\x02\x01'
shoff=struct.unpack_from('<Q',b,40)[0];ents,n,si=struct.unpack_from('<HHH',b,58)
rows=[struct.unpack_from('<IIQQQQIIQQ',b,shoff+i*ents) for i in range(n)];strings=b[rows[si][4]:rows[si][4]+rows[si][5]]
sections={strings[r[0]:].split(b'\0',1)[0].decode():r for r in rows}
r=sections['.rodata'];raw=b[r[4]:r[4]+r[5]];text=sections['.text'];slots={}
for name,value in [('pool',0x41),('registry',0x44)]:
 needle=bytes([value])*32;positions=[i for i in range(len(raw)-31) if raw[i:i+32]==needle];found=[]
 for i in positions:
  addr=r[3]+i;refs=[]
  for j in range(text[4],text[4]+text[5]-8,8):
   if b[j]==0x18:
    imm=struct.unpack_from('<I',b,j+4)[0]|(struct.unpack_from('<I',b,j+12)[0]<<32)
    if imm in [addr,addr+0x100000000]:refs.append(dict(file_offset=j,virtual_address=text[3]+j-text[4],immediate=imm,instructions_hex=b[j:j+16].hex()))
  found.append(dict(file_offset=r[4]+i,virtual_address=addr,bytes_hex=needle.hex(),lddw_references=refs))
 slots[name]=found
symbols=subprocess.run(['readelf','-sW',str(p)],capture_output=True,text=True,check=True).stdout
x=dict(status='PINNED_DEFAULT_SLOT_CANDIDATES_ONLY; ASSOCIATION_OPEN',artifact=dict(path=str(p),sha256=h,bytes=len(b)),slots=slots,static_symbols_present=('AUDIT_POOL_PROGRAM' in symbols or 'AUDIT_REGISTRY_PROGRAM' in symbols),symbol_table=symbols,source_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',limitation='Unique bytes and lddw immediates alone do not associate a specific source black_box use or the devnet override; historical K3 evidence remains denied. No deployed helper closure.',print_axioms='N/A: read-only ELF inventory')
(B/'NHD_RODATA.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps({k:v for k,v in x.items() if k!='symbol_table'}))
