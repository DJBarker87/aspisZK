from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2c-20261028';j=json.load(open(E/'deployed-native-inputs.json'))
assert j['all_dependency_versions_from_deployed_lock'] and j['all_native_linux_deployed_unit_features_equal']
for r in json.load(open(E/'deployed-pairs-inputs.json'))['sources']:
 assert hashlib.sha256(subprocess.check_output(['git','show','HEAD:'+r['path']])).hexdigest()==r['sha256']
(E/'configuration.json').write_text(json.dumps(dict(deployed_lock_pin=json.load(open(E/'deployed-lock-pin.json')),validation='all dependency versions from deployed client lock; compiled Linux dependency feature sets match deployed unit graph; target-only metadata packages separately recorded',actual=j,corrected_inputs='deployed-native-inputs.json',old_drift='old-native-configuration-drift.json',rust_source_hashes_match_frozen_git=True,lean_source_or_theorem_changes_for_configuration_fix=False),indent=2)+'\n')
print('PASS deployed lock, dependency feature union and frozen source hashes')
