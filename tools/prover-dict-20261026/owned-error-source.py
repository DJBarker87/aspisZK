"""Cut exact owned-reference bodies; associate the identical42-case ErrorKind."""
from pathlib import Path
import re,json,hashlib
r=Path(__file__).resolve().parents[2];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/owned7/emission';p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/PDict_OwnedErrorSource.lean'
t=(e/'Types.lean.txt').read_text();f=(e/'Funs.lean.txt').read_text();b=(r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullTypes.lean').read_text()
def constructors(s):
 z=s.split('inductive core.io.error.ErrorKind where\n')[1].split('\n/--')[0]
 return re.findall(r'^\| (\w+) : core.io.error.ErrorKind$',z,re.M)
a=constructors(t);old=constructors(b);assert a==old and len(a)==42,(a,old)
structs=t[t.index('structure owned_error.OwnedError'):t.index('\nend PDict_OwnedErrorSource')]
bodies=f.split('namespace PDict_OwnedErrorSource\n',1)[1].split('\nend PDict_OwnedErrorSource')[0]
bodies=bodies.replace('core.io.error.ErrorKind.AlreadyExists','ProverRwFull.core.io.error.ErrorKind.AlreadyExists')
s='''import R1Z.PDict_ErrorKind
set_option autoImplicit false
namespace PDict_OwnedErrorSource
open Aeneas Aeneas.Std Result
/-- Same42constructors as the baseline reference emission; associated with
its already-extracted core ErrorKind, not with dynamic std.io.Error. -/
abbrev core.io.error.ErrorKind := ProverRwFull.core.io.error.ErrorKind
'''+structs+'\n'+bodies+'\n'
for n in ['core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq','owned_error.owned_observe','owned_error.owned_open_error','owned_error_observe','owned_error_open']:s+=f'\n#print axioms {n}'
s+='\nend PDict_OwnedErrorSource\n';p.write_text(s)
(e/'source-cut.json').write_text(json.dumps(dict(emitted_source_hashes={q.name:hashlib.sha256(q.read_bytes()).hexdigest() for q in e.glob('*.lean.txt')},source_module_sha256=hashlib.sha256(s.encode()).hexdigest(),normalization='Only imports, stripped generated resource options, exact42-constructor ErrorKind association with the AlreadyExists constructor qualified, concatenation of unchanged owned structs/function bodies, and axiom audit commands.',kind_constructors=a,native_dynamic_error_association=False),indent=2)+'\n')
