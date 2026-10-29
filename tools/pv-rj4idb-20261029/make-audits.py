"""Reproduce/check the corrected frozen combined audit and single replay."""
from pathlib import Path
import json,sys
E=Path('evidence/pv-rj4idb-20261029');freeze=json.loads((E/'proof-source-freeze.json').read_text())
names=freeze['new_theorem_names'];defs=freeze['open_input_definitions'];mods=[v['module'] for v in freeze['modules']]
root_checks=['R1Z.PV_RJDec_CommonCases.complete_pair','R1Z.PV_RJDec_ResultCases.fibres_iff','R1Z.PV_RJDec_V047Native.consume','R1Z.PV_RJ4IDB_NativePowers.deployed_installation','R1Z.PV_RJ4IDB_CallerSemantic.caller_to_transfer13','R1Z.PV_RJ4IDB_CallerSemantic.consume','PV_RJ4IDB.native_factorization','PV_RJ4IDB.all_prefixes','PV_RJ4IDB.result_fibres_exact']
s='import R1Z.PV_RJDec_CommonCases\n'+''.join('import '+m+'\n' for m in mods)
s+='/-! Complete checked types; native producer inputs remain OPEN Props, not instances. -/\n'+''.join('#check '+n+'\n' for n in names+defs+root_checks)
s+='\n/-! Combined corrected full-statement and every-theorem axioms audit. -/\n'+''.join('#print axioms '+n+'\n' for n in names+defs+root_checks[:3])
r='import PV_RJ4IDB_Axioms\n/-! Single final focused cached manifest; NOT a whole privacy release replay. -/\n'+''.join('#check '+n+'\n#print axioms '+n+'\n' for n in root_checks)
for name,text in [('Axioms',s),('Replay',r)]:
 p=Path('lean/PV_RJ4IDB_'+name+'.lean')
 if '--check' in sys.argv:assert p.read_text()==text,('audit generator mismatch',p)
 else:p.write_text(text)
print('corrected frozen audit generator check passed' if '--check' in sys.argv else 'corrected frozen audit sources written')
