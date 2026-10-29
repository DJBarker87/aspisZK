from pathlib import Path
import re,json
D=Path(__file__).parent
files=sorted(p for p in D.glob('PV_DIAG10_*.lean') if not any(x in p.stem for x in ['Audit','FinalManifest']))
main=[];op=[]
for p in files:
 names=re.findall(r'^(?:theorem|def|inductive)\s+(\w+)',p.read_text(),re.M)
 (op if p.stem=='PV_DIAG10_Op227' else main).extend(names)
s='import PV_DIAG10_Handoff\nimport PV_DIAG9_Encoders\n'
s+=''.join('#print axioms PV_DIAG10.'+n+'\n' for n in main)
(D/'PV_DIAG10_Audit.lean').write_text(s)
s='import PV_DIAG10_Op227\n'+''.join('#print axioms PV_DIAG10.'+n+'\n' for n in op)
s+='#print axioms PV_B3P_Success227.installed_success8\n#print axioms PV_B3P_Success227.installed_nonvacuity8\n'
(D/'PV_DIAG10_Op227Audit.lean').write_text(s)
s='''import PV_DIAG10_Audit
set_option autoImplicit false
namespace PV_DIAG10
open PV_RJ4IDB
theorem frozen_manifest {I A : Type}
 (files : I → List FileOp) (json : I → List Bytes × List (Bytes × Bytes))
 (errors : I → List PV_DIAG2.Effect × List PV_DIAG3.Event)
 (native : I → NativeTrace A) (raw : I → List NativeEvent)
 (fr : PV_DIAG10_Link_Readout files sourceFile raw)
 (jr : PV_DIAG10_Link_Readout json sourceJSON raw)
 (er : PV_DIAG10_Link_Readout errors sourceError raw)
 (order : PV_DIAG10_Link_EventOrder raw native) :
 OpenInputs.DIAG_FILE_TRACE files native ∧
 OpenInputs.DIAG_JSON_STDOUT_TRACE json native ∧
 OpenInputs.DIAG_ERROR_STDERR_TRACE errors native :=
 all_three_exact_inputs files json errors native raw fr jr er order
#print axioms frozen_manifest
end PV_DIAG10
'''
(D/'PV_DIAG10_FinalManifest.lean').write_text(s)
(D/'audit-coverage.json').write_text(json.dumps(dict(main=main,op227=op,final=['frozen_manifest'],new_theorems=sum(len(re.findall(r'^theorem ',p.read_text(),re.M)) for p in files)+1),indent=2)+'\n')
print('main',len(main),'op',len(op))
