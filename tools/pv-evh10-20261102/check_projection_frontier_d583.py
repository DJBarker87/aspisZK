"""Read-only D583 actual installation review; does not create a run witness."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

E = Path('evidence/pv-evh10-20261102')
sha = lambda b: hashlib.sha256(b).hexdigest()
runtime = Path('lean/PV_EVH_RuntimeBinding.lean').read_text()
fields = []
for field, projection in [
    ('native', '<same run.events, faithful native terminal>'),
    ('fileTrace', 'PV_RJ4IDB.nativeFiles run.events'),
    ('countTrace', '(PV_RJ4IDB.nativeCounts run.events, PV_RJ4IDB.nativeRejections run.events)'),
    ('timeTrace', 'PV_RJ4IDB.nativeTimes run.events'),
    ('oraclePrefix', 'PV_RJ4IDB.nativeOracle run.events'),
]:
    assert re.search(r'^  ' + field + r' := missing\.' + field + r'_OPEN$', runtime, re.M)
    fields.append(dict(field=field, current=field + '_OPEN', required=projection, installed=False))
assert 'success : ' in Path('lean/PV_EVH_NativeEntropyIteration.lean').read_text()
assert 'def entry_OPEN' in Path('lean/PV_EVH_NativeOperatorProver.lean').read_text()
world = Path('lean/PV_EVH_World.lean').read_text().split('structure World where')[1].split('structure Run')[0]
assert 'rsp' not in world and 'stack' not in world and 'mapping' not in world
tracked = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', 'HEAD', 'lean'], text=True).splitlines()
owner_hits = [p for p in tracked if p.endswith('.lean') and
              'OWNER_actual_prefix' in Path(p).read_text()]
assert not owner_hits, owner_hits
paths = ['lean/PV_EVH_RuntimeBinding.lean', 'lean/PV_EVH_World.lean',
         'lean/PV_EVH_StackCleanup.lean', 'lean/PV_EVH_NativeEntropyIteration.lean',
         'lean/PV_EVH_NativeOperatorProver.lean', 'lean/PV_RJ4IDB_NativeTrace.lean',
         'BLOCKER-evhB.md', str(E / 'FRAME-ENTRY-D583.md'), str(E / 'BLOCKER-D583.md'), __file__]
result = dict(
    evidence_class='read-only actual installation frontier; no runtime instance',
    inputs=[dict(path=p, sha256=sha(Path(p).read_bytes())) for p in paths],
    shared_OWNER_literal_export_hits=owner_hits,
    shared_OWNER_not_supplied_by_this_review=True,
    domain='unchanged actual entry arguments/capture and all reached prefix/world outcomes',
    required_dictionary='opsNative (PV_EVH_NativeRawSelection.rawBase base) heap box ops',
    fields=fields, actual_advancing_run_installed=False,
    five_projections_installed=False, successful_actual_nonemptiness_proved=False,
    rows_removed=[], trust_fields_added=[],
    next_lean=90259, next_native='N91603', host_runs=0, lean_attempts=0,
    stop='shared OWNER not merged; actual advancing full producer absent; inherited focus rule')
p = E / 'projection-frontier-D583.json'
if '--check' in sys.argv:
    assert json.loads(p.read_text()) == result
else:
    p.write_text(json.dumps(result, indent=2) + '\n')
print('PASS five OPEN selectors and actual-run blocker recorded; no projection installation claimed')
