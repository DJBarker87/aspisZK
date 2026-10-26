#!/usr/bin/env python3
"""Literal derived-field bodies from the retained actual source extraction."""
from pathlib import Path
import re,json,hashlib,sys
r=Path(__file__).resolve().parents[3]
p=r/'docs/research/100bit-spend-path-20261013/lean-candidates/s9-current-qraw-ebyk-source-body-v1-20261023/upstream/AspisR1S9ProductionPairCutV1/Funs.lean'
s=p.read_text()
names=['aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq','aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq','aspis_core.field.QM31.Insts.CoreCloneClone.clone','aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq']
blocks={}
for name in names:
 m=re.search(r'\bdef\s+'+re.escape(name)+r'\b',s);assert m,name
 blocks[name]=s[m.start():s.index('\n/--',m.end())].strip()
t='''import R1Z.ProverRwFullTypes
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
namespace R1Z.ProverRwDictionaryDerivedSource

'''+ '\n\n'.join(blocks.values())+'\n\nend R1Z.ProverRwDictionaryDerivedSource\n'
o=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwDictionaryDerivedSource.lean'
if '--check' in sys.argv:assert o.read_text()==t
else:o.write_text(t)
x=dict(source=str(p.relative_to(r)),source_sha256=hashlib.sha256(s.encode()).hexdigest(),declarations={n:hashlib.sha256(b.encode()).hexdigest() for n,b in blocks.items()},output_sha256=hashlib.sha256(t.encode()).hexdigest(),scope='Literal emitted bodies rebound to the identical full-caller field shapes; native ABI association remains open')
if '--check' not in sys.argv:(r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/native-install/derived-source.json').write_text(json.dumps(x,indent=2)+'\n')
print(x['output_sha256'])
