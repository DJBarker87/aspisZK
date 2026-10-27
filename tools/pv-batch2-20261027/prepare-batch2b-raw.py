"""Exact raw extraction modules; only import routing and shift-count API compatibility.
The numeric shift counts are unchanged. No theorem is supplied by this adapter.
"""
from pathlib import Path
import hashlib,json,re,sys
D=Path('evidence/pv-batch2-20261027/batch2b/batch2b-extraction-10');L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');outputs={};pins=[]
for op in [251,253]:
 g=D/f'generated-{op}';t=(g/'Types.lean').read_text();f=(g/'Funs.lean').read_text();ns=f'PV_B2_{op}b10';tm=f'PV_B2_RawWeights{op}Types';fm=f'PV_B2_RawWeights{op}Funs'
 assert not list(g.glob('*External*'))
 assert f.count('31#i32')==2
 assert all('wrapping_shr' in line for line in f.splitlines() if '31#i32' in line)
 assert len(re.findall(r'(?<![0-9])1#i32',f))==1
 assert f.count('Std.U16.wrapping_shr i1 i2')==1
 f=f.replace('31#i32','31#u32').replace('1#i32','1#u32').replace('Std.U16.wrapping_shr i1 i2','Std.U16.wrapping_shr i1 (UScalar.cast .U32 i2)').replace(f'import PVB2{op}.Types',f'import R1Z.{tm}')
 assert f'import R1Z.{tm}' in f
 td=re.findall(r'^(?:def|structure|inductive) ([\w.]+)',t,re.M);fd=re.findall(r'^def ([\w.]+)',f,re.M)
 outputs[L/(tm+'.lean')]=t+'\n'+''.join('#print axioms '+ns+'.'+d+'\n' for d in td)
 outputs[L/(fm+'.lean')]='-- Adapter: private import, three unsigned shift literals, one low-word shift-count cast.\n'+f+'\n'+''.join('#print axioms '+ns+'.'+d+'\n' for d in fd)
 pins.append(dict(op=op,raw_types_sha256=hashlib.sha256((g/'Types.lean').read_bytes()).hexdigest(),raw_funs_sha256=hashlib.sha256((g/'Funs.lean').read_bytes()).hexdigest(),functions=len(fd),types=len(td),root='pv_b2_materialize' if op==251 else 'pv_b2_raw',opaque_declarations=0,adaptations=['private module import','three unsigned shift literals; identical numeric counts31/31/1','U16 wrapping shift count narrowed from Usize to U32; low4bits preserved; generic modular cast law required']))
for p,s in outputs.items():
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
j=dict(pins=pins,outputs={str(p):hashlib.sha256(s.encode()).hexdigest() for p,s in outputs.items()})
p=D.parent/'RAW-PREFLIGHT.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==j
else:p.write_text(json.dumps(j,indent=2)+'\n')
print('checked' if '--check' in sys.argv else 'prepared',len(outputs),'raw modules')
