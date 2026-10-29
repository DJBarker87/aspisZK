from pathlib import Path
import re,json,hashlib
D=Path(__file__).resolve().parent
sets={'Audit':['Boundary','Fd','WriteAll','Open'],'ProducerAudit':['Buffer','Line','JSONStdout','Composition']}
coverage={}
for suffix,names in sets.items():
 s=''.join('import PV_DIAG12_'+n+'\n' for n in names)
 for n in names:
  p=D/('PV_DIAG12_'+n+'.lean');ns=re.findall(r'^theorem (\w+)',p.read_text(),re.M)
  coverage[p.stem]=ns
  s+=''.join('#print axioms PV_DIAG12.'+v+'\n' for v in ns)
 (D/('PV_DIAG12_'+suffix+'.lean')).write_text(s)
(D/'PV_DIAG12_FinalManifest.lean').write_text('''import PV_DIAG12_Audit
import PV_DIAG12_ProducerAudit
import PV_DIAG10_Handoff
/- One focused source-layer manifest. No deployed Link instance is asserted.
All three original typed acquisition inputs retain their unchanged links. -/
#check PV_DIAG10.DIAG_FILE_TRACE
#check PV_DIAG10.DIAG_JSON_STDOUT_TRACE
#check PV_DIAG10.DIAG_ERROR_STDERR_TRACE
#print axioms PV_DIAG10.DIAG_FILE_TRACE
#print axioms PV_DIAG10.DIAG_JSON_STDOUT_TRACE
#print axioms PV_DIAG10.DIAG_ERROR_STDERR_TRACE
#print axioms PV_DIAG12.jsonStream_append
#print axioms PV_DIAG12.onePrintln_chunks_append
#print axioms PV_DIAG12.pending_prefix_readout
''')
(D/'audit-coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
print('audit coverage',sum(map(len,coverage.values())))
