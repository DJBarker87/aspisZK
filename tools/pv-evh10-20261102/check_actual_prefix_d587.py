"""Pinned D587 source inspection. No execution, reachability, or proof credit."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

BASE = '7356208133e924f6caabb8e2136a370ee6f02035'
E = Path('evidence/pv-evh10-20261102')
paths = [
    'lean/PV_EVH_PhysicalFrame.lean',
    'lean/PV_EVH_FrameTransitions.lean',
    'lean/PV_EVH_FrameSource.lean',
    'lean/PV_EVH_FrameWorld.lean',
    'lean/PV_EVH_Prefix.lean',
    'lean/PV_EVH_World.lean',
    'lean/PV_EVH_Runtime.lean',
    'lean/PV_EVH_StackZero.lean',
    'lean/PV_EVH_EntropyDeployedLayout.lean',
    'lean/PV_EVH_NativeOperatorProver.lean',
    'lean/PV_EVH_NativeEntropyIteration.lean',
    'lean/PV_EVH_RuntimeBinding.lean',
    str(E / 'FRAME-D585.md'),
    str(E / 'BLOCKER-D585.md'),
    str(E / 'FRAME-ENTRY-D583.md'),
    str(E / 'inputs-D584/SHARED-VEC-D580.md'),
    str(E / 'inputs-D584/prompt-pv-evhB4.txt'),
]
sources = {}
pins = []
for path in paths:
    raw = subprocess.check_output(['git', 'show', BASE + ':' + path])
    assert Path(path).read_bytes() == raw, ('inspected source changed', path)
    sources[path] = raw.decode()
    pins.append(dict(path=path, sha256=hashlib.sha256(raw).hexdigest(),
                     git_blob=subprocess.check_output(
                         ['git', 'rev-parse', BASE + ':' + path], text=True).strip()))

# Exact-name inventory across ALL tracked Lean paths, not just lean/.
# This checks textual declarations only; it is not semantic nonexistence.
names = ['ActualEntropyEntryPrefix', 'OWNER_actual_prefix', 'actual_frame_entry']
pattern = (r'(^|[[:space:]])(def|abbrev|structure|inductive|theorem|opaque|axiom)'
           r'[[:space:]]+([[:alnum:]_]+\.)?(' + '|'.join(names)
           + r')([^[:alnum:]_]|$)')
scan = subprocess.run(['git', 'grep', '-n', '-E', pattern, BASE, '--', '*.lean'],
                      capture_output=True, text=True)
assert scan.returncode == 1 and not scan.stdout and not scan.stderr, scan
tree = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASE], text=True)
lean_paths = [p for p in tree.splitlines() if p.endswith('.lean')]

frame = sources['lean/PV_EVH_FrameSource.lean']
assert '(ActualEntropyEntryPrefix : Type)' in frame
assert 'view : ActualEntropyEntryPrefix → EntryView' in frame
assert 'opsNative (rawBase base) heap box ops' in frame
for field in ['state', 'thread', 'activation', 'sp', 'loadBias', 'stackLimit',
              'retry', 'iteration', 'retryHistory', 'answer']:
    assert re.search(r'^  ' + field + r' :', frame, re.M), field
for field in ['state_eq', 'retry_eq', 'limit_eq', 'mask_backing']:
    assert re.search(r'^  ' + field + r' :', frame, re.M), field
world = sources['lean/PV_EVH_World.lean'].split('structure World where')[1].split('structure Run')[0]
assert not re.search(r'\b(rip|rsp|memory|stackAnswer|loadBias|mapping)\b', world)
assert 'abbrev P (A : Type) := World → Prefix A' in sources['lean/PV_EVH_Prefix.lean']
layout = sources['lean/PV_EVH_EntropyDeployedLayout.lean']
assert '(hl : ∀ old ∈ w.frame.live' in layout
assert '(hh : ∀ b ∈ w.frame.runtime.heap' in layout
assert '(success :' in sources['lean/PV_EVH_NativeEntropyIteration.lean']
entry = sources['lean/PV_EVH_NativeOperatorProver.lean']
assert 'def entry_OPEN' in entry and '(frame_fixed :' in entry
selectors = ['native', 'fileTrace', 'countTrace', 'timeTrace', 'oraclePrefix']
for field in selectors:
    assert re.search(r'^  ' + field + r' := missing\.' + field + r'_OPEN$',
                     sources['lean/PV_EVH_RuntimeBinding.lean'], re.M), field

result = dict(
    source_revision=BASE,
    evidence_class='source inspection; binary interpretation remains binary-structural plus V370',
    sources=pins,
    declaration_inventory=dict(names=names, tracked_lean_paths=len(lean_paths),
                               paths_sha256=hashlib.sha256(('\n'.join(lean_paths)+'\n').encode()).hexdigest(),
                               hits=[], scope='exact textual declaration names only'),
    actual_prefix_producer_constructed=False,
    actual_correspondence_instantiated=False,
    actual_frame_entry_proved=False,
    concrete_shared_OWNER_Prop_available=False,
    full_source_live_slot_binding_proved=False,
    open_runtime_selectors=selectors,
    counterexample_to_shipped_source=False,
    lean_attempts=0, native_attempts=0, host_scopes=0,
    new_axioms_audit=None, inherited_axioms_mode='SUMMARY-BASED',
    next_lean=90267, next_native='N91603',
    endpoint_rows_removed=[], new_hypotheses=[], new_trust_fields=[],
)
out = E / 'actual-prefix-D587.json'
if '--check' in sys.argv:
    assert json.loads(out.read_text()) == result
else:
    out.write_text(json.dumps(result, indent=2) + '\n')
print('PASS D587 source inventory; actual-family construction remains incomplete')
