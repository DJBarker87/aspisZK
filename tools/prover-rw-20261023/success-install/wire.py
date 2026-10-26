"""Literal retained wire error/domain bodies; read-only --check mode."""
from pathlib import Path
import hashlib,json,re,sys
r=Path(__file__).resolve().parents[3]
p=r/'docs/research/100bit-spend-path-20261013/evidence/lean-record-source-20261015/header-parser-f/AspisR1RecordParser/Funs.lean'
s=p.read_text();n='r1_wire.Error.Insts.CoreCmpPartialEqError.eq';m=re.search(r'^def\s+'+re.escape(n)+r'(?=\s|\{)',s,re.M);b=s[m.start():s.index('\n/--',m.end())].strip()
p2=r/'docs/research/100bit-spend-path-20261013/evidence/finish-point-and-terminal-call-20261018/compatibility/canonical-Funs.lean';s2=p2.read_text();m=re.search(r'^def r1_wire.DOMAIN',s2,re.M);d=s2[m.start():s2.index('\n/--',m.end())].strip()
t='''import R1Z.ProverRwSuccessEquality
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessWireSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
'''+d+'\nend R1Z.ProverRwSuccessWireSource\n'
o=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwSuccessWireSource.lean'
if '--check' in sys.argv:assert o.read_text()==t
else:o.write_text(t)
print(hashlib.sha256(t.encode()).hexdigest())
