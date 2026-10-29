from pathlib import Path
import re
E=Path(__file__).parent
modules=sorted(p.stem for p in E.glob('PV_DIAG3_*.lean') if not p.stem.endswith(('Audit','FinalManifest')))
names=[]
for module in modules:
 names += re.findall(r'^theorem (\w+)',(E/(module+'.lean')).read_text(),re.M)
assert len(names)==len(set(names))
(E/'PV_DIAG3_Audit.lean').write_text('import PV_DIAG3_Observer\nimport PV_DIAG3_Syswrite\n\n'+ '\n'.join('#print axioms PV_DIAG3.'+n for n in names)+'\n#print axioms R1Z.ProverRwRetryModel.retry\n#print axioms R1Z.ProverCommitRetry34.run\n')
(E/'PV_DIAG3_FinalManifest.lean').write_text('import PV_DIAG3_Audit\n\n/-! One final job manifest, not the frozen whole-privacy release closure. -/\n#print axioms PV_DIAG3.public_joint_function\n#print axioms PV_DIAG3.client_joint_trace_transport\n#print axioms PV_DIAG3.complete_observer_transport\n#print axioms PV_DIAG3.result_only_decoder_requires_prefix_agreement\n')
print('audit modules',len(modules),'theorems',len(names))
