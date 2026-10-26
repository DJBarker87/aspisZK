"""Pin the freshly emitted current wire Error equality; no body rewriting."""
from pathlib import Path
import hashlib,re,json,sys
r=Path(__file__).resolve().parents[3];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-next';p=e/'error-generated-005/Funs.lean';s=p.read_text();n='r1_wire.Error.Insts.CoreCmpPartialEqError.eq';m=re.search(r'^def '+re.escape(n)+r'\b',s,re.M);assert m
b=s[m.start():s.index('\n/--',m.end())].strip();assert 'ActivePole' in b
# Both enums must have exactly the same constructor declarations after nominal qualification.
t=(e/'error-generated-005/Types.lean').read_text();f=(r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullTypes.lean').read_text()
pat=r'inductive r1_wire.Error where\n([\s\S]*?)\n\n'
a=re.search(pat,t);c=re.search(pat,f);assert a and c and a[1]==c[1]
o=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwSuccessErrorSource.lean';out='''import R1Z.ProverRwSuccessHeapInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessErrorSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
'''+b+'\nend R1Z.ProverRwSuccessErrorSource\n'
if '--check' in sys.argv:assert o.read_text()==out
else:
 o.write_text(out);(e/'error-source.json').write_text(json.dumps(dict(source=str(p.relative_to(r)),source_sha256=hashlib.sha256(s.encode()).hexdigest(),declaration_sha256=hashlib.sha256(b.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),enum_constructors_identical=True,changes='Namespace and import only; exact body and identical existing Full enum and discriminant. Current r1p-check ActivePole is included.'),indent=2)+'\n')
