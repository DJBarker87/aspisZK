from pathlib import Path
import json,re
D=Path(__file__).resolve().parent
mods=list(json.loads((D/'plans.json').read_text()))
groups=[('PV_DIAG11_Audit',mods[:7]),('PV_DIAG11_ProducerAudit',mods[7:])]
coverage={}
for name,ms in groups:
 s='\n'.join('import '+m for m in ms)+'\n'
 for m in ms:
  ns=re.findall(r'^theorem (\w+)',(D/(m+'.lean')).read_text(),re.M)
  coverage[m]=ns
  for n in ns:s+='#print axioms PV_DIAG11.'+n+'\n'
 (D/(name+'.lean')).write_text(s)
(D/'PV_DIAG11_FinalManifest.lean').write_text('''import PV_DIAG11_Audit
import PV_DIAG11_ProducerAudit
import PV_DIAG10_Handoff
/-! One focused local manifest; not the frozen privacy-release manifest.
The three DIAG inputs remain conditional. No new Link definition or instance. -/
#check PV_DIAG10.DIAG_FILE_TRACE
#check PV_DIAG10.DIAG_JSON_STDOUT_TRACE
#check PV_DIAG10.DIAG_ERROR_STDERR_TRACE
#print axioms PV_DIAG10.DIAG_FILE_TRACE
#print axioms PV_DIAG10.DIAG_JSON_STDOUT_TRACE
#print axioms PV_DIAG10.DIAG_ERROR_STDERR_TRACE
#print axioms PV_DIAG11.writeAll_same_length_metadata
#print axioms PV_DIAG11.unit_error_operand_link
''')
(D/'audit-coverage.json').write_text(json.dumps(dict(modules=coverage,theorems=sum(map(len,coverage.values()))),indent=2)+'\n')
