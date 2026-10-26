"""Tiny independent 10x28 polynomial diagnostic; not a release gate or Lean proof."""
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];E=Path(__file__).resolve().parent
proof=[]
for f in sorted((R/'lean').glob('JFx_DataProof[0-9][0-9].lean')):
 for line in f.read_text().splitlines():
  if line.startswith('def c'):
   if 'List.replicate' in line:
    n,v=map(int,re.search(r'List.replicate (\d+) (\d+)#u8',line).groups());proof.extend([v]*n)
   else:proof.extend(map(int,re.findall(r'(\d+)#u8',line)))
assert len(proof)==57607
b=bytes(proof);at=48;frames=[];payloads=[]
for row in range(27):
 header=b[at:at+5];at+=5;n=int.from_bytes(header[1:],'little')
 if row>=14:
  payload=b[at:at+n//2];at+=n//2
  payload=b''.join(payload[i:i+16]+bytes(16) for i in range(0,len(payload),16))
 else:payload=b[at:at+n];at+=n
 assert len(payload)==n
 frames.append(header+payload);payloads.append(payload)
assert at==7031
pub=bytes(json.loads((E/'JFu_SERIALIZATION_DIAGNOSTIC.json').read_text())['semantic_bytes'])
domain=bytes.fromhex(json.loads((E/'JFu_SEED_DIAGNOSTIC.json').read_text())['domain_hex'])
state=hashlib.sha256(domain+b'\0'+len(pub).to_bytes(4,'little')+pub+b[16:48]).digest();seed=state
P=2147483647
def add(x,y):return tuple((a+b)%P for a,b in zip(x,y))
def cmul(x,y):return ((x[0]*y[0]-x[1]*y[1])%P,(x[0]*y[1]+x[1]*y[0])%P)
def mul(x,y):
 a=cmul(x[:2],y[:2]);c=cmul(x[2:],y[2:]);d=cmul(add(x[:2],x[2:]),add(y[:2],y[2:]));r=((2*c[0]-c[1])%P,(c[0]+2*c[1])%P)
 return add(a,r)+tuple((d[i]-a[i]-c[i])%P for i in range(2))
def decode(x):return tuple(int.from_bytes(x[i:i+4],'little') for i in range(0,16,4))
qs=[];calls=[]
for row,frame in enumerate(frames):
 absorbed=hashlib.sha256(state+bytes([0,160+row])+frame).digest()
 block=hashlib.sha256(absorbed+b'\1').digest();state=hashlib.sha256(absorbed+b'\2').digest()
 rank=int.from_bytes(block,'little');digits=[]
 for _ in range(4):rank,d=divmod(rank,P);digits.append(d)
 qs.append(tuple(digits));calls.extend([(state.hex(),block.hex())])
running=decode(payloads[14][:16]);rounds=[]
for r in range(10):
 coeffs=[decode(payloads[15+r][i:i+16]) for i in range(0,896,32)]
 boundary=coeffs[0]
 for q in coeffs:boundary=add(boundary,q)
 value=(0,0,0,0)
 for c in reversed(coeffs):value=add(mul(value,qs[15+r]),c)
 rounds.append(dict(round=r,running=running,boundary=boundary,passes=boundary==running,value=value,alpha=qs[15+r]))
 running=value
out=dict(kind='independent Python diagnostic, not kernel certificate',proof_sha256=hashlib.sha256(b).hexdigest(),seed=seed.hex(),rounds=rounds,all_boundaries=all(r['passes'] for r in rounds),circle_blocks=calls[25:])
(E/'JFu_ARITHMETIC_DIAGNOSTIC.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['seed'],out['all_boundaries'],[r['round'] for r in rounds if not r['passes']])
