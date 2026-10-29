"""D438 allocator-boundary check. Negative certificate, no root executions.

Revalidate the captured source and release-object cohort, then check an
outside-box foreign-call witness. Never traverse or classify allocator reads.
"""
from pathlib import Path
import hashlib, json, re, subprocess, time

R = Path(__file__).resolve().parents[2]
E = R / 'evidence/pv-owng-20261029'
assert R == Path('/Users/dominic/ZK/.worktrees/pv-own')
assert subprocess.check_output(['git', 'branch', '--show-current'], text=True).strip() == 'codex/pv-owng-20261029'
sha = lambda b: hashlib.sha256(b).hexdigest()
prior_path = R / 'evidence/pv-owne-20261029/static-capture.json'
native_path = E / 'native-result.json'
prior = json.loads(prior_path.read_bytes())
native = json.loads(native_path.read_bytes())
records = []
for s in prior['sources']:
    assert sha(s['text'].encode()) == s['sha256']
    if 'git_blob' in s:
        assert sha(subprocess.check_output(['git', 'show', 'HEAD:' + s['relative_path']])) == s['sha256']
    records.append({k: s[k] for k in ['path', 'relative_path', 'size', 'sha256']})
pins = records + native['inputs'] + [native['binary']]
remote = '''
import json,hashlib,subprocess
from pathlib import Path
for p in PINS:
 b=Path(p['path']).read_bytes()
 assert len(b)==p['size'] and hashlib.sha256(b).hexdigest()==p['sha256'],p['path']
commands={}
for n,c in COMMANDS.items():
 q=subprocess.run(c,capture_output=True,text=True)
 assert q.returncode==0,(n,q.stderr)
 commands[n]=q.stdout
print(json.dumps(dict(commands=commands,checked_files=len(PINS))))
'''.replace('PINS', repr(pins)).replace('COMMANDS', repr({
    n: native['commands'][n]['command'] for n in ['disassembly', 'relocations', 'rustc']
}))
start = time.monotonic()
q = subprocess.run(['ssh', 'dombarker@100.108.41.90', 'python3', '-'], input=remote, capture_output=True, text=True)
assert q.returncode == 0, q.stderr
checked = json.loads(q.stdout)
for n, value in checked['commands'].items():
    assert value == native['commands'][n]['stdout'], n
dis = checked['commands']['disassembly']
rel = checked['commands']['relocations']
funcs = {m[2]: m[0] for m in re.finditer(r'^([0-9a-f]+) <([^\n]+)>:\n(.*?)(?=\n[0-9a-f]+ <|\Z)', dis, re.M | re.S)}
prefix = 'aspis_statement::pool_v1::'
rows = funcs[prefix + 'pair_forest_hiding::pool_v1_pair_forest_copy_active_rows_v1']
masks = funcs[prefix + 'pair_forest_hiding::pool_v1_pair_forest_copy_active_row_masks_v1']
forest = funcs[prefix + 'pair_forest_hiding::build_pool_v1_pair_forest_copy_row_schedule_v1']
tree = funcs[prefix + 'pair_tree_hiding::build_pool_v1_pair_copy_row_schedule_v1']
for address, target in [('5d170', '18a50'), ('5d250', '18dd0'), ('5d218', '19620')]:
    assert re.search(r'^0*' + address + r'\s+.*R_X86_64_RELATIVE\s+' + target + r'$', rel, re.M)
assert re.search(r'^0*5d240\s+.*memset@GLIBC_2.2.5', rel, re.M)
assert re.search(r'18ca5:.*call.*5d170', masks)
assert re.search(r'18a64:.*call.*5d250', rows)
assert re.search(r'18df3:.*call.*5d218', forest)
assert re.search(r'19b59:.*mov.*5d240.*memset', tree)
for a in ['19b67', '19b79']:
    assert re.search(a + r':.*call\s+\*%r14', tree)
assert 'mov    $0x400,%edx' in tree
texts = {s['relative_path']: s['text'] for s in prior['sources']}
t = texts['crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs']
f = texts['crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs']
assert 'endpoint_counts(&links)?;' in t
assert 'let mut producers = [0u8; 1024];' in t
assert 'let mut consumers = [0u8; 1024];' in t
assert 'let mut links = build_pool_v1_pair_copy_row_schedule_v1()?' in f
assert 'let mut rows = build_pool_v1_pair_forest_copy_row_schedule_v1()?' in f
assert 'for row in pool_v1_pair_forest_copy_active_rows_v1()?' in f
out = dict(
    rule="own-2''", worktree=str(R),
    source_revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
    checker_sha256=sha(Path(__file__).read_bytes()),
    captures=[dict(path=str(p.relative_to(R)), sha256=sha(p.read_bytes())) for p in [prior_path, native_path]],
    checked_files=checked['checked_files'],
    allocator_boundary=['alloc', 'realloc', 'dealloc', 'EVERYTHING executed below those entries'],
    withdrawn_witnesses=['malloc initialization byte', 'malloc tcache TLS', '__libc_single_threaded', 'free errno save/restore'],
    qualification='NOT ESTABLISHED: outside-box foreign memset calls in original-root release cohort',
    witness=dict(callee='memset@GLIBC_2.2.5', got='0x5d240', caller='legacy schedule builder: inlined endpoint_counts', calls=['0x19b67', '0x19b79'], size=1024, value=0,
                 root_path=['V230 -> V229', 'V229 -> forest schedule builder', 'forest schedule builder -> legacy schedule builder', 'endpoint_counts array initialization -> libc memset']),
    excerpts=dict(rows=rows, masks=masks, forest=forest, tree=tree),
    artifact_scope='Pinned deployed-configuration statement rlib linked into diagnostic probe; NOT a claimed execution of the shipped client artifact',
    address_independence='Not certified for whole cone; foreign-call obstruction prevents qualification',
    channel_iii='Not certified for whole cone; no allocator-internal read used as an obstruction',
    inspection=dict(exit=0, wall_seconds=time.monotonic()-start, peak_rss='N/A read-only inspection', swap='N/A', print_axioms='N/A no Lean declarations'),
    spent=dict(lean=0, native_scopes=1, kani=0),
)
(E / 'static-capture.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps({k: out[k] for k in ['qualification', 'checked_files', 'witness', 'inspection', 'spent']}, indent=2))
