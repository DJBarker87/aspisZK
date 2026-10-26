"""Emit bounded literal data chunks; no proof/native acceptance is inferred."""
from pathlib import Path
import hashlib,json,argparse,re
ROOT=Path(__file__).resolve().parents[2]
E=ROOT/'evidence/joint-fixture-20261026'
P=ROOT/'docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/transfer-13'
parser=argparse.ArgumentParser()
parser.add_argument('--checkpoint',type=Path)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
def retained_checkpoint():
 if args.checkpoint:return args.checkpoint.read_bytes()
 # The literal source is retained as data; no binary or temporary path is required.
 b=bytearray()
 for line in (ROOT/'lean/JFx_DataCheckpoint00.lean').read_text().splitlines():
  if line.startswith('def c'):
   term=line.split(':=',1)[1]
   if 'List.replicate' in term:
    n,v=map(int,re.search(r'List.replicate (\d+) (\d+)#u8',term).groups());b.extend([v]*n)
   else:b.extend(map(int,re.findall(r'(\d+)#u8',term)))
 return bytes(b)
data={'Proof':(P/'r1-s2-proof.bin').read_bytes(),'Public':(P/'r1-s2-public-asf8.bin').read_bytes(),'Checkpoint':retained_checkpoint()}
assert hashlib.sha256(data['Checkpoint']).hexdigest()=='6c9f774dd0032d3df18c9724c38d02c5225f31808a4cfe8560c210dc4d3dc625'
assert hashlib.sha256(data['Proof']).hexdigest()=='55386c507d3feeebfc45272a1cf15c33ccb9ccf0a8a8f41180fc654d806fff6f'
assert hashlib.sha256(data['Public']).hexdigest()=='f6bcd49446f1077d2c5ed4be940e91f0be444efc5ae83024ec0700b8c205c331'
manifest={'classification':'Literal data from retained successful native pair; not an accepted Lean execution','inputs':{},'modules':[]}
for kind,b in data.items():
 manifest['inputs'][kind]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 for part,start in enumerate(range(0,len(b),4096)):
  raw=b[start:start+4096];mod=f'JFx_Data{kind}{part:02d}';out=['import Aeneas','set_option autoImplicit false','namespace AspisR1.'+mod,'open Aeneas Aeneas.Std']
  cs=[]
  for i,lo in enumerate(range(0,len(raw),32)):
   chunk=raw[lo:lo+32];name=f'c{i:02d}';cs.append(name)
   if len(set(chunk))==1:
    term=f'List.replicate {len(chunk)} {chunk[0]}#u8'
    proof='by simp only ['+name+',List.length_replicate]'
   else:
    term='['+','.join(f'{v}#u8' for v in chunk)+']'
    proof='by simp only ['+name+',List.length_cons,List.length_nil]'
   out += [f'def {name} : List U8 := {term}',f'theorem {name}_length : {name}.length = {len(chunk)} := {proof}',f'#print axioms {name}_length']
  
  def balanced(xs):
   if len(xs)==1:return xs[0]
   mid=len(xs)//2
   return '('+balanced(xs[:mid])+' ++ '+balanced(xs[mid:])+')'
  out += ['def bytes : List U8 := '+balanced(cs),f'theorem length : bytes.length = {len(raw)} := by', '  simp only [bytes,List.length_append,'+','.join(c+'_length' for c in cs)+']','#print axioms length','end AspisR1.'+mod]
  text='\n'.join(out)+'\n'
  target=ROOT/'lean'/f'{mod}.lean'
  if args.check:assert target.read_text()==text,mod
  else:target.write_text(text)
  manifest['modules'].append({'module':mod,'kind':kind,'offset':start,'bytes':len(raw),'data_sha256':hashlib.sha256(raw).hexdigest(),'source_sha256':hashlib.sha256(text.encode()).hexdigest()})
if args.check:assert json.loads((E/'JFx_DATA.json').read_text())==manifest
else:(E/'JFx_DATA.json').write_text(json.dumps(manifest,indent=2)+'\n')
