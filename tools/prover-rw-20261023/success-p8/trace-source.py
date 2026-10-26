"""Literal cfg-selected trace callback; only the nominal WideExact type is aliased."""
from pathlib import Path
import hashlib,json,sys
r=Path(__file__).resolve().parents[3];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-p8'
s=(e/'trace-value-Funs.lean.txt').read_text();a=s.index('/-- [aspis_r1_cost_probe::trace::value]');b=s.index('\nend PV_TraceValue',a)
body=s[a:b];assert 'ok ()' in body and 'def trace.value' in body
out='''import R1Z.PV_CurrentDictionary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_TraceValueSource
open Aeneas Aeneas.Std Result ControlFlow Error
abbrev aspis_core.field.wide_exact.WideExact := ProverRwFull.aspis_core.field.wide_exact.WideExact
'''+body+'''
theorem exact (tag : U16) (index : Usize) (x : aspis_core.field.wide_exact.WideExact) :
    trace.value tag index x = ok () := rfl
#print axioms exact
end R1Z.PV_TraceValueSource
'''
p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_TraceValueSource.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:
 p.write_text(out)
 (e/'trace-value-source-map.json').write_text(json.dumps(dict(raw_sha256=hashlib.sha256(s.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),profile=['optimized-terminal','ct-host-prover'],changes='Literal value body; nominal WideExact carrier alias; independent exact theorem; generated headers/options omitted. No observer/TLS/model law is asserted.'),indent=2)+'\n')
