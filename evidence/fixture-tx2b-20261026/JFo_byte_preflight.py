from pathlib import Path
import re,hashlib,json
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent

def data(path):
 s=path.read_text();out=[]
 for txt in re.findall(r'^def c\d+ : List U8 := ([^\n]*)',s,re.M):
  rep=re.fullmatch(r'List.replicate (\d+) (\d+)#u8',txt)
  out.extend([int(rep[2])]*int(rep[1]) if rep else [int(b) for b in re.findall(r'(\d+)#u8',txt)])
 return bytes(out)
proof=b''.join(data(R/f'lean/JFx_DataProof{i:02}.lean') for i in range(15))
public=data(R/'lean/JFx_DataPublic00.lean');checkpoint=data(R/'lean/JFx_DataCheckpoint00.lean')
assert (len(proof),len(public),len(checkpoint))==(57607,1880,1768)
h=lambda b:hashlib.sha256(b).hexdigest()
assert bytes.fromhex(h(proof))==checkpoint[16:48]
assert bytes.fromhex(h(public))==checkpoint[48:80]
assert bytes.fromhex(h(b'UNPROVED:R1:checkpoint'+checkpoint[:1736]))==checkpoint[1736:]
v={'classification':'Executable diagnostic only; not a Lean SHA256 theorem, oracle instance, or accepted2 proof','lengths':{'proof':len(proof),'public':len(public),'checkpoint':len(checkpoint)},'sha256':{'proof':h(proof),'public':h(public),'checkpoint':h(checkpoint),'checksum':h(b'UNPROVED:R1:checkpoint'+checkpoint[:1736])},'three_checkpoint_hash_cells_match':True}
(P/'JFo_BYTE_PREFLIGHT.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v))
