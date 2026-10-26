"""Copy three retained parser bodies; no recurrence evaluation or new extraction."""
from pathlib import Path
import re,hashlib,json,sys
r=Path(__file__).resolve().parents[3]
p=r/'docs/research/100bit-spend-path-20261013/lean/CandidateFieldParsers.lean'
s=p.read_text();blocks=[];pins={}
for n in ['field.M31.from_le_bytes','field.CM31.from_le_bytes','field.QM31.from_le_bytes']:
 m=re.search(r'\bdef '+re.escape(n)+r'\b',s);assert m
 b=s[m.start():s.index('\n/--',m.end())].strip();pins[n]=hashlib.sha256(b.encode()).hexdigest()
 b=b.replace('field.','aspis_core.field.').replace('core.option.Option.Insts.','ProverRwDictionaryOptionSource.core.option.Option.Insts.')
 blocks.append(b)
t='''import R1Z.ProverRwDictionaryBytesSource
import R1Z.ProverRwDictionaryOptionSource
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
namespace R1Z.ProverRwSuccessParserSource
abbrev aspis_core.field.P := ProverRwDictionaryBytesSource.aspis_core.field.P
'''+ '\n\n'.join(blocks)+'\nend R1Z.ProverRwSuccessParserSource\n'
o=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwSuccessParserSource.lean'
if '--check' in sys.argv: assert o.read_text()==t
else:
 o.write_text(t)
 e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-install'
 (e/'parser-source.json').write_text(json.dumps(dict(path=str(p.relative_to(r)),source_sha256=hashlib.sha256(s.encode()).hexdigest(),declarations=pins,output_sha256=hashlib.sha256(t.encode()).hexdigest(),rewrites='Nominal field type qualification, explicit retained option operations, P alias only. No altered guards, slicing, failures or constructor behavior.'),indent=2)+'\n')
print(hashlib.sha256(t.encode()).hexdigest())
