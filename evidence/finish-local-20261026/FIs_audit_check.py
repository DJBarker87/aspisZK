from pathlib import Path
import json,re
E=Path(__file__).resolve().parent
logs={next((p/'sources').glob('*.lean')).stem:(p/'stdout.log').read_text() for p in sorted(E.glob('FIs_[0-9][0-9][0-9]')) if (p/'stdout.log').exists()}
fin=logs['FIs_AuditFinish'];pair=logs['FIs_AuditFinishLaws'];lit=logs['FIs_AuditLiteral'];result=logs['FIs_AuditResultBinding']
assert 'FIs_Pair.Law' in fin
assert 'SAF_ReducedLaws.Arithmetic' not in fin and 'dot_S5' not in fin
assert 'FIs_Finish.Outcome' in lit and 'FIs_Caller.Outcome' in result
assert 'FIs_Pair.Law' in pair and 'RoundPairing.dualFold' in pair
# Check only the actual AFTER type, not imported old declarations or proof terms.
root=(E/'FIs_AFTER.lean.txt').read_text()
assert 'FIs_Result.Outcome' in root
for forbidden in ['FIs_Native.Calls','SAG_NativeFull.Shape','FIn_FromRead','FIs_OnRun','FIs_Pair.Law']:
 assert forbidden not in root,forbidden
out=dict(new_native_finish='Pair/matching/three semantic endpoints only',no_new_shape_or_arithmetic_root_input=True,exact_root_statement_check=json.loads((E/'FIs_statement-check.json').read_text()),checked_inventory_modules=['FIs_AuditFinish','FIs_AuditFinishLaws','FIs_AuditLiteral','FIs_AuditResultBinding'])
(E/'FIs_audit-check.json').write_text(json.dumps(out,indent=2)+'\n')
print('Native finish inventory and root-input checks passed.')
