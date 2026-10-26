"""Check the single proved clone substitution in the actual continuation."""
from pathlib import Path
import sys,json,hashlib
r=Path(__file__).resolve().parents[3];d=r/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=(d/'ProverRwBodyStoreSource.lean').read_text()
a='''aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone
        compiled.semantic_c1''';assert s.count(a)==1
out=s.replace('import R1Z.ProverRwFullFuns','import R1Z.ProverRwP7TraceCloneInstall').replace('R1Z.ProverRwBodyStoreSource','R1Z.ProverRwP7BodyCloneSource').replace(a,'ok compiled.semantic_c1')
p=d/'ProverRwP7BodyCloneSource.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:
 p.write_text(out)
 e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-p7'
 (e/'body-clone-source-map.json').write_text(json.dumps(dict(original_sha256=hashlib.sha256(s.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),changes='Imports and namespace plus exactly one clone callee replaced by its proved returned value. All later source calls, errors, audit and state remain literal.'),indent=2)+'\n')
