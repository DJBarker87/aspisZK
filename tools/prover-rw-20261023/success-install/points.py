"""Retain statement-point loop and wrapper with nominal arithmetic maps."""
from pathlib import Path
import re,hashlib,sys,json
r=Path(__file__).resolve().parents[3]
p=r/'docs/research/100bit-spend-path-20261013/evidence/s9-actual-weights-new-sourcecut-v4-20261023/sources/checked/Funs.lean'
s=p.read_text();names=['state_only_prefix.state_only_statement_points_loop.body','state_only_prefix.state_only_statement_points_loop','state_only_prefix.state_only_statement_points','state_only_prefix.r0.statement_points'];blocks=[];pins={}
for n in names:
 m=re.search(r'^def\s+'+re.escape(n)+r'(?=\s|\{)',s,re.M);assert m,n
 b=s[m.start():s.index('\n/--',m.end())].strip();blocks.append(b);pins[n]=hashlib.sha256(b.encode()).hexdigest()
t='''import R1Z.ProverRwSuccessWideSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessPointsSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwDictionaryTower
abbrev field.QM31 := Q
abbrev field.QM31.mul := qMul
abbrev field.QM31.add := qAdd
abbrev field.QM31.sub := qSub
def field.QM31.ONE : Q := fromQ AspisR1ProducerRelease47.field.QM31.ONE
'''+ '\n\n'.join(blocks)+'\nend R1Z.ProverRwSuccessPointsSource\n'
o=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwSuccessPointsSource.lean'
if '--check' in sys.argv:assert o.read_text()==t
else:
 o.write_text(t)
 (r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-resume/points-source.json').write_text(json.dumps(dict(source=str(p.relative_to(r)),sha256=hashlib.sha256(s.encode()).hexdigest(),declarations=pins,output_sha256=hashlib.sha256(t.encode()).hexdigest(),rewrite='Namespace and literal arithmetic-carrier maps only; reverse traversal, reads, updates and Result constructors retained'),indent=2)+'\n')
print(hashlib.sha256(t.encode()).hexdigest())
