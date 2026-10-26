"""Literal actual retained field bodies rebound to full caller field shapes."""
from pathlib import Path
import re,json,hashlib,sys
r=Path(__file__).resolve().parents[3]
p=r/'docs/research/100bit-spend-path-20261013/lean-candidates/s9-current-qraw-ebyk-source-body-v1-20261023/upstream/AspisR1S9ProductionPairCutV1/Funs.lean'
q=r/'docs/research/100bit-spend-path-20261013/lean/OraclePortCkptAbi2Extracted/Funs.lean'
t=r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwSampler/Funs.lean'
requests=[(p,['aspis_core.field.P','aspis_core.field.wide_exact.WideExact.BYTE_LEN','aspis_core.field.wide_exact.WideExact.from_limbs','aspis_core.field.wide_exact.WideExact.to_limbs','aspis_core.field.wide_exact.WideExact.from_le_bytes']),(q,['aspis_core.field.M31.to_le_bytes','aspis_core.field.CM31.write_le_bytes','aspis_core.field.QM31.write_le_bytes']),(t,['aspis_core.field.CM31.new'])]
blocks=[];pins=[]
for path,names in requests:
 s=path.read_text();d={}
 for name in names:
  m=re.search(r'\bdef\s+'+re.escape(name)+r'\b',s);assert m,name
  b=s[m.start():s.index('\n/--',m.end())].strip();blocks.append(b);d[name]=hashlib.sha256(b.encode()).hexdigest()
 pins.append(dict(path=str(path.relative_to(r)),sha256=hashlib.sha256(s.encode()).hexdigest(),declarations=d))
body='''import R1Z.ProverRwFullTypes
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
namespace R1Z.ProverRwDictionaryBytesSource

'''+ '\n\n'.join(blocks)+'\nend R1Z.ProverRwDictionaryBytesSource\n'
o=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwDictionaryBytesSource.lean'
if '--check' in sys.argv:assert o.read_text()==body
else:
 o.write_text(body)
 (r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/native-install/bytes-source.json').write_text(json.dumps(dict(inputs=pins,output_sha256=hashlib.sha256(body.encode()).hexdigest(),scope='Literal retained real-source declarations; nominal field rebind only, full errors/divergence preserved. Native association remains open.'),indent=2)+'\n')
print(hashlib.sha256(body.encode()).hexdigest())
