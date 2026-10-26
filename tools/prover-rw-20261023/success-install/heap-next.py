from pathlib import Path
import re,json,hashlib,sys
r=Path(__file__).resolve().parents[3];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-next';out=r/'docs/research/v8-r0-zk-20261009/lean/R1Z'
p=r/'docs/research/100bit-spend-path-20261013/lean-candidates/s9-current-qraw-ebyk-source-body-v1-20261023/upstream/AspisR1S9ProductionPairCutV1/Funs.lean';s=p.read_text();names=['aspis_core.r0.heap.filled.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError.call_once','aspis_core.r0.heap.filled.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError','aspis_core.r0.heap.filled'];blocks=[];pins={}
for n in names:
 m=re.search(r'^def\s+'+re.escape(n)+r'(?=\s|\{)',s,re.M);assert m,n
 b=s[m.start():s.index('\n/--',m.end())].strip();pins[n]=hashlib.sha256(b.encode()).hexdigest();blocks.append(b)
t='''import R1Z.ProverRwSuccessBodyInterpretation
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessHeapSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Global := Unit
abbrev aspis_core.r0.heap.filled.closure (T : Type) := Unit
'''+ '\n\n'.join(blocks)+'''
end R1Z.ProverRwSuccessHeapSource
'''
o=out/'ProverRwSuccessHeapSource.lean'
if '--check' in sys.argv:
 assert o.read_text()==t
 raise SystemExit(0)
o.write_text(t)
(e/'heap-source.json').write_text(json.dumps(dict(source=str(p.relative_to(r)),sha256=hashlib.sha256(s.encode()).hexdigest(),declarations=pins,output_sha256=hashlib.sha256(t.encode()).hexdigest(),changes='Nominal namespace; erased Global allocator carrier Unit; allocation callback retained. Native allocator and generic library adequacy remain open.'),indent=2)+'\n')
