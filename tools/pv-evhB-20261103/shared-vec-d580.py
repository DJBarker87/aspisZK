"""Read-only source/anchor inventory. This does not prove native correspondence."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

START = 'c1b31fa688727ff7e4a08216557f25eccb2a7a1e'
V263 = 'a5b8b16cf10ae7fa94a493a4e4723cefd83d3d1c'
EVIDENCE = Path('evidence/pv-evhB-20261103')
PREFIX = 'docs/research/v8-r0-zk-20261009/lean/R1Z/'
STD = 'evidence/pv-v263-20261102/inputs/std-1.94.1/alloc/src/'


def read(rev, path):
    return subprocess.check_output(['git', 'show', f'{rev}:{path}'])


def pin(rev, path, anchors=()):
    raw = read(rev, path)
    source = raw.decode()
    found = []
    for anchor in anchors:
        assert anchor in source, (path, anchor)
        found.append({'text': anchor, 'line': source[:source.index(anchor)].count('\n') + 1})
    return {'revision': rev, 'path': path,
            'git_blob': subprocess.check_output(
                ['git', 'rev-parse', f'{rev}:{path}'], text=True).strip(),
            'sha256': hashlib.sha256(raw).hexdigest(), 'bytes': len(raw),
            'anchors': found}


rows = [
    pin('c770b853f02302d48c9e8172468426402b9df440', PREFIX +
        'PV_RunJoin_AllocatorWorld63.lean', ('metadata : World S F', 'def execute')),
    pin('eb2d028a96d6061f2aed4c693aaad46790768d5d', PREFIX +
        'PV_FXM_ReserveSelected.lean', ('structure Metadata', 'Result.ok (returned encode e.returned,v)')),
    pin('eb2d028a96d6061f2aed4c693aaad46790768d5d', PREFIX +
        'PV_FXM_ReserveWorld.lean', ('Option Nat × S', 'def finish', 'def native')),
    pin(V263, 'evidence/pv-v263-20261102/BLOCKER-D579.md'),
    pin(V263, STD + 'raw_vec/mod.rs', ('unsafe fn grow_amortized(',
        'unsafe fn finish_grow(', 'const unsafe fn set_ptr_and_cap(',
        'self.ptr = Unique::from(ptr.cast());',
        'self.cap = unsafe { Cap::new_unchecked(cap) };', 'unsafe fn grow_exact(')),
    pin(V263, STD + 'vec/mod.rs', ('pub fn push_mut(',
        'ptr::write(end, value);', 'self.len = len + 1;', 'pub fn try_reserve_exact(')),
    pin(V263, PREFIX + 'PV_V263_MapSpine.lean',
        ('| push (site thread oldLength : Nat) (layout : Layout)', 'vector : VecCall → Q S Unit')),
    pin(V263, PREFIX + 'PV_V263_RetainedMethods.lean', ('def push',)),
    pin(V263, PREFIX + 'PV_V263_RetainedSpine.lean', ('def forks',)),
    pin(V263, PREFIX + 'PV_V263_RawGrowth.lean', ('structure Runtime', 'def store')),
    pin(V263, PREFIX + 'PV_V263_GrowingPush.lean', ('def push', 'theorem reserved')),
    pin(V263, PREFIX + 'PV_V263_OwnedDrain.lean', ('structure Owner',)),
    pin(V263, PREFIX + 'PV_V263_BufferLoop.lean', ('def mapAction',)),
    pin(V263, PREFIX + 'PV_V263_World.lean', ('inductive Outcome', 'structure Run')),
    pin(START, 'lean/PV_EVH_Runtime.lean', ('structure State', 'inductive Outcome')),
    pin(START, 'lean/PV_EVHB_SaltsReserve.lean', ('def afterReserve', 'theorem selected_prefix')),
    pin(START, 'lean/PV_EVHB_PrivateSaltStep.lean', ('push_OPEN :', 'push_fixed :')),
]
old = json.loads(read(START, 'evidence/pv-evh8-20261101/allocator-sources.json'))
old_raw = next(f['sha256'] for f in old['files'] if f['path'].endswith('/raw_vec/mod.rs'))
new_raw = next(r['sha256'] for r in rows if r['path'] == STD + 'raw_vec/mod.rs')
assert old_raw == new_raw
summary_path = 'evidence/pv-evhB-20261103/summary.json'
assert read(START, summary_path) == Path(summary_path).read_bytes()
summary = json.loads(Path(summary_path).read_text())
assert summary['remaining_attempts'] == 74 and summary['next_normal_id'] == 91222
record = {
    'evidence_class': 'read-only pinned-source inspection; NOT a native binding or Lean proof',
    'resume_revision': START, 'v263_revision': V263, 'sources': rows,
    'raw_vec_sha256_match': old_raw, 'generic_correspondence': 'OPEN',
    'reached_reserve_header_delivery': 'OPEN', 'v263_D579_instance': 'OPEN',
    'reached_counterexample': 'not established',
    'attempts_this_resume': 0, 'next_normal_id': 91222, 'remaining_attempts': 74,
    'audit_91298_91299': 'unused', 'host_launches': 0, 'native_runs': 0,
    'kani_runs': 0, 'extractions': 0, 'new_axiom_audits': 0,
    'endpoint_rows_removed': [], 'premises_added_or_changed': [], 'trust_fields_added': [],
    'historical_summary_sha256': hashlib.sha256(Path(summary_path).read_bytes()).hexdigest(),
}
output = json.dumps(record, indent=2, ensure_ascii=False) + '\n'
destination = EVIDENCE / 'shared-vec-D580.json'
if '--check' in sys.argv:
    assert destination.read_text() == output
else:
    destination.write_text(output)
print(f'{len(rows)} source pins/anchors checked; RawVec hashes match; native correspondence OPEN; next91222/74 left')
