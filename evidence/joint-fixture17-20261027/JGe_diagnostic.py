from pathlib import Path
import re,hashlib,json
P=Path(__file__).resolve().parent; R=P.parents[1]
def extract(f):
 out=[]
 for l in f.read_text().splitlines():
  if l.startswith('def c'):
   if 'replicate' in l:
    n,v=map(int,re.search(r'replicate (\d+) (\d+)#u8',l).groups());out += [v]*n
   else:out += list(map(int,re.findall(r'(\d+)#u8',l)))
 return bytes(out)
proof=b''.join(extract(R/f'lean/JFx_DataProof{i:02}.lean') for i in range(15));assert len(proof)==57607
rs=re.findall(r'def result : Reg := ⟨([^⟩]*)⟩',(R/'lean/JFu_Q26Reads.lean').read_text())
seed=b''.join(int(x).to_bytes(4,'big') for x in rs[-1].split(','))
sha=lambda b:hashlib.sha256(b).digest()
state=sha(b'UNPROVED:R1:PRIVATE-SALTED:P3'+bytes([2])+seed)
# The extracted domain is exactly 29 bytes, with UNPROVED prefix.
state=sha(bytes([85,78,80,82,79,86,69,68,58,82,49,58,80,82,73,86,65,84,69,45,83,65,76,84,69,68,58,80,51])+bytes([2])+seed)
y1=b''.join(proof[i:i+16]+bytes(16) for i in range(7031,7495,16))
payloads={27:y1,28:bytes(32),29:proof[7527:7751],30:proof[7751:8007],31:proof[8007:10055],32:b''}
messages={'Init':bytes([85,78,80,82,79,86,69,68,58,82,49,58,80,82,73,86,65,84,69,45,83,65,76,84,69,68,58,80,51])+bytes([2])+seed};rows={}
for row,payload in payloads.items():
 absorb=state+bytes([0,160+row])+len(payload).to_bytes(4,'little')+payload
 messages[f'Q{row}Absorb']=absorb;absorbed=sha(absorb)
 count=8 if row==31 else 1;blocks=[];advances=[]
 for i in range(count):
  messages[f'Q{row}Read{i}']=absorbed+b'\x01';messages[f'Q{row}Ratchet{i}']=absorbed+b'\x02'
  blocks.append(sha(absorbed+b'\x01'));absorbed=sha(absorbed+b'\x02');advances.append(absorbed)
 state=advances[2] if row==31 else advances[-1];rows[row]={'blocks':[b.hex() for b in blocks],'advances':[b.hex() for b in advances]}
check={}
for row,name in [(27,'Gamma'),(28,'Kappa'),(29,'Alpha0'),(30,'Alpha1'),(32,'Rho')]:
 vals=re.search(r'def bytes : List U8 := \[(.*?)\]',(R/f'lean/JFq_{name}.lean').read_text())[1]
 checkpoint=bytes(map(int,re.findall(r'(\d+)#u8',vals)))
 check[name]={'checkpoint':checkpoint.hex(),'block':rows[row]['blocks'][0]}
(P/'JGe_OPENING_DIAGNOSTIC.json').write_text(json.dumps({'kind':'diagnostic only; no acceptance or equality proof','seed':seed.hex(),'rows':rows,'comparisons':check,'messages':{k:list(v) for k,v in messages.items()},'sha_blocks':sum((len(v)+9+63)//64 for v in messages.values())},indent=2)+'\n')
print(json.dumps({'sha_blocks':sum((len(v)+9+63)//64 for v in messages.values()),'comparisons':check,'final_state':state.hex()},indent=2))
