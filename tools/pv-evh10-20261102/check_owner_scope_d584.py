"""D584 source-frontier certificate, not an execution/refinement proof."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

E = Path('evidence/pv-evh10-20261102')
shared = E / 'inputs-D584/SHARED-VEC-D580.md'
prompt = E / 'inputs-D584/prompt-pv-evhB4.txt'
branch_rev = (E / 'inputs-D584/branch-revision.txt').read_text().strip()
assert shared.read_bytes() == subprocess.check_output(
    ['git', 'show', branch_rev + ':SHARED-VEC-D580.md'])
assert 'SOURCE-BOUND OWNER LOOKUP' in prompt.read_text()
assert 'size cap*size_of::<T>()' in prompt.read_text()
assert 'PRESERVATION through every RawVec operation' in prompt.read_text()
assert 'new assumed equality would not meet' in shared.read_text()

paths = [
    'lean/PV_EVH_RuntimeBinding.lean',
    'lean/PV_EVH_NativeOperatorProver.lean',
    'lean/PV_EVH_NativeEntropyIteration.lean',
    'lean/PV_EVH_NativeEntropyDelivered.lean',
    'lean/PV_EVH_NativeEntropyRejected.lean',
    'lean/PV_EVH_World.lean',
    'lean/PV_EVH_Runtime.lean',
    'lean/PV_EVH_StackCleanup.lean',
    'lean/PV_EVH_StackZero.lean',
    'lean/PV_EVH_EntropyDeployedLayout.lean',
    'lean/PV_RJ4IDB_Channels.lean',
    'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_FXM_ReserveWorld.lean',
    str(E / 'FRAME-ENTRY-D583.md'),
    str(E / 'BLOCKER-D583.md'),
    str(E / 'BLOCKER-D584.md'),
    str(shared), str(prompt), str(E / 'inputs-D584/branch-revision.txt'),
    'tools/pv-evh10-20261102/check_owner_scope_d584.py',
]
source = {p: Path(p).read_text() for p in paths}
runtime = source[paths[0]]
selectors = ['native', 'fileTrace', 'countTrace', 'timeTrace', 'oraclePrefix']
for field in selectors:
    assert re.search(r'^  ' + field + r' := missing\.' + field + r'_OPEN$',
                     runtime, re.M), field
assert 'def entry_OPEN' in source[paths[1]]
assert '(account_fixed :' in source[paths[1]]
assert '(frame_fixed :' in source[paths[1]]
assert '(success :' in source[paths[2]]
assert 'PV_EVH_KernelMemory.ValidAnswer' in source[paths[3]]
assert 'PV_EVH_KernelMemory.ValidAnswer' in source[paths[4]]
world = source[paths[5]].split('structure World where')[1].split('structure Run')[0]
assert not re.search(r'\b(stack|mapping|rsp|stackAnswer)\b', world)
assert '| fault (error : Fault)' in source[paths[6]]
assert '| exhausted' in source[paths[6]]
assert '| abort (value : PV_DIAG3.Crash)' in source[paths[10]]
assert 'live : Nat → Bool' in source[paths[11]]

# Only an exact-name declaration inventory, not a semantic absence proof.
tracked = subprocess.check_output(
    ['git', 'ls-tree', '-r', '--name-only', 'HEAD', 'lean'], text=True).splitlines()
names = ['ActualEntropyEntryPrefix', 'OWNER_actual_prefix',
         'actual_frame_entry', 'stackAnswer']
hits = []
pattern = re.compile(r'^\s*(?:def|abbrev|structure|inductive|theorem)\s+('
                     + '|'.join(names) + r')\b', re.M)
for path in tracked:
    if path.endswith('.lean'):
        hits.extend({'path': path, 'name': m.group(1)}
                    for m in pattern.finditer(Path(path).read_text()))
assert not hits, hits

result = {
    'resume_revision': '062167fb6868fb08d5dcea8ac442380d2e200fd6',
    'shared_branch_revision_read_only': branch_rev,
    'evidence_class': 'source-frontier inspection; no formal execution proof',
    'inputs': [{'path': p, 'sha256': hashlib.sha256(Path(p).read_bytes()).hexdigest()}
               for p in paths],
    'exact_semantic_placeholder_declarations': hits,
    'open_runtime_selectors': selectors,
    'owner_scope': 'source Vec/RawVec allocator ownership and operation preservation',
    'D583_broader_owner_reduction_claim_withdrawn': True,
    'waiting_for_shared_branch': False,
    'single_exact_OWNER_Prop_implemented': False,
    'conditional_actual_frame_entry_proved': False,
    'complete_advancing_producer_implemented': False,
    'simultaneous_projections_installed': False,
    'counterexample_to_shipped_source': False,
    'host_runs': 0, 'lean_attempts': 0, 'new_axioms_audit': None,
    'rows_removed': [], 'new_hypotheses': [], 'new_trust_fields': [],
    'next_lean': 90259, 'next_native': 'N91603',
}
out = E / 'owner-scope-D584.json'
if '--check' in sys.argv:
    assert json.loads(out.read_text()) == result
else:
    out.write_text(json.dumps(result, indent=2) + '\n')
print('PASS D584 pinned OWNER scope and concrete source frontier; construction incomplete')
