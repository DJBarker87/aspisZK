#!/usr/bin/env python3
"""Verify the saved R366 formal evidence and byte-identical promoted source; no Lean invocation."""
from pathlib import Path
import hashlib, json, re, sys

ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[4]
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''): h.update(block)
    return h.hexdigest()

def verify_sum_file(root, name='SHA256SUMS'):
    index=root/name
    files={p.relative_to(root).as_posix():p for p in root.rglob('*') if p.is_file() and p != index}
    rows={}
    for line in index.read_text().splitlines():
        digest, rel=line.split('  ',1)
        assert rel not in rows, f'duplicate checksum row: {rel}'
        assert rel in files, f'checksum path absent: {rel}'
        assert sha(files[rel])==digest, f'checksum mismatch: {rel}'
        rows[rel]=digest
    assert set(rows)==set(files), f'{name} does not cover exact files in {root}'
    return len(rows)

# Top-level checksums cover all payload and metadata files except themselves.
package_files={p.relative_to(ROOT).as_posix():p for p in ROOT.rglob('*') if p.is_file() and p != ROOT/'SHA256SUMS'}
verify_sum_file(ROOT)
# No compiled artifact or build cache is shipped; .olean hashes inside JSON metadata are not files.
for rel in package_files:
    p=Path(rel)
    assert not any(part=='__pycache__' for part in p.parts), f'cache directory included: {rel}'
    assert p.suffix.lower() not in {'.olean','.ilean','.cmi','.cmo','.cmx','.o','.a','.pyc','.exe','.so'}, f'compiled artifact included: {rel}'
    assert p.name!='R366SemanticNormalization.olean', f'compiled target object included: {rel}'

formal=json.loads((ROOT/'formal.json').read_text())
receipt=json.loads((ROOT/'attempts/02-successful/receipt.json').read_text())
failed=json.loads((ROOT/'attempts/01-missing-cache/receipt.json').read_text())
assert formal['successful_compile']['exit_status']==0==receipt['exit_status']
assert formal['successful_compile']['source_sha256']==receipt['source_sha256']
assert formal['source_revision']==receipt['source_revision']
assert formal['failed_attempt']['exit_status']==1==failed['exit_status']
assert 'StructuredCube.olean' in formal['failed_attempt']['first_error']
assert 'StructuredCube.olean' in (ROOT/'attempts/01-missing-cache/lean.log').read_text()
production=REPO/formal['production_path']
success_src=ROOT/'attempts/02-successful/source.lean'
assert production.is_file() and sha(production)==formal['production_sha256']==receipt['source_sha256']==sha(success_src)
assert sha(ROOT/'sources/R366SemanticNormalization.current-draft.lean')==formal['production_sha256']
assert sha(ROOT/'sources/R366SemanticNormalization.successful-compile-input.lean')==formal['production_sha256']
assert sha(ROOT/'attempts/01-missing-cache/source.lean')==failed['source_sha256']
# Check portable archived copies; original scratch and promoted repository copies are optional provenance checks.
graph=json.loads((ROOT/'copygraph.json').read_text())
ignore_scratch='--ignore-scratch' in sys.argv
for node in graph['nodes']:
    archived=ROOT/node['archived_path']
    assert archived.is_file() and sha(archived)==node['sha256'], f"archived copygraph node mismatch: {node['archived_path']}"
    if not ignore_scratch and node.get('original_scratch_path'):
        original=REPO/node['original_scratch_path']
        if original.exists(): assert sha(original)==node['sha256'], f"available scratch provenance differs: {node['original_scratch_path']}"
    if node.get('repo_path'):
        promoted=REPO/node['repo_path']
        assert promoted.is_file() and sha(promoted)==node['sha256'], f"promoted source mismatch: {node['repo_path']}"
for edge in graph['edges']:
    a=ROOT/edge['from_archived']; b=ROOT/edge['to_archived']
    assert a.is_file() and b.is_file() and sha(a)==sha(b), f"archived copygraph edge mismatch: {edge}"
# The successful log contains every complete theorem axiom report in the saved receipt.
success_log=(ROOT/'attempts/02-successful/lean.log').read_text()
for line in receipt['complete_print_axioms']:
    assert line in success_log, f'missing target #print axioms line: {line}'
assert len(receipt['complete_print_axioms'])==6
# Replay all nested dependency files without rebuilding anything.
replay_root=ROOT/'dependency-cache-replay'
cache_root=ROOT/'lean-cache-inventory'
verify_sum_file(replay_root)
verify_sum_file(cache_root)
replay=json.loads((replay_root/'replay-summary.json').read_text())
cache=json.loads((cache_root/'inventory.json').read_text())
report_count=sum(len(t.get('complete_print_axioms',[])) for t in replay['targets'])
assert replay['compiled_dependency_count']==11 and replay['all_exit_zero'] is True and replay['all_swap_zero'] is True
assert replay['R366_target_compiled'] is False and report_count==57
assert cache['counts']['local_dependency_modules']==23 and cache['counts']['cached_local_objects']==12 and len(cache['counts']['missing_local_objects'])==11
assert cache['counts']['missing_external_import_objects']==[]
assert formal['dependency_cache_replay']['named_theorem_axiom_reports']==57
# Validate target theorem names, exact resource metrics, and standard foundation names.
expected_target_names=[
    'AspisR19.R366SemanticNormalization.finite_expansion',
    'AspisR19.R366SemanticNormalization.normalized_round',
    'AspisR19.R366SemanticNormalization.normalized_walk',
    'AspisR19.R366SemanticNormalization.structured_sub',
    'AspisR19.R366SemanticNormalization.terminal_compatibility',
    'AspisR19.R366SemanticNormalization.full_271_compatibility',
]
def report_axioms(line):
    match=re.search(r'depends on axioms: \[(.*?)\]$',line)
    assert match, f'malformed complete axiom report: {line}'
    found=[x.strip() for x in match.group(1).split(',') if x.strip()]
    assert set(found)<= {'propext','Classical.choice','Quot.sound'}, f'nonstandard foundation in report: {found}'
    return found
assert len(receipt['complete_print_axioms'])==6
success_log_text=(ROOT/'attempts/02-successful/lean.log').read_text()
assert 'Maximum resident set size (kbytes): 2064980' in success_log_text and 'Swaps: 0' in success_log_text and 'Exit status: 0' in success_log_text
for line,name in zip(receipt['complete_print_axioms'],expected_target_names):
    assert line.startswith(f"'{name}' "), f'target axiom report name mismatch: {line}'
    assert set(report_axioms(line))=={'propext','Classical.choice','Quot.sound'}
assert receipt['peak_rss_kib']==2064980 and receipt['swaps']==0 and receipt['wall_time']=='0:01.48'
assert receipt['resources']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'lean_flags':'-j1 -M4500'}
# Validate each of the 11 saved dependency receipts, source/log binding, and all 57 verbatim reports.
total_dependency_reports=0
assert len(replay['targets'])==11
for row in replay['targets']:
    assert row['exit_status']==0 and row['swaps']==0
    assert row['source_revision']==formal['source_revision']
    receipt_path=replay_root/row['local_receipt']
    dep=json.loads(receipt_path.read_text())
    assert dep['target']==row['module'].replace('.', '/')+'.lean'
    assert dep['exit_status']==row['exit_status'] and dep['swaps']==row['swaps']
    assert dep['source_revision']==row['source_revision']==formal['source_revision']
    assert dep['runner_sha256']==row['runner_sha256']==receipt['runner_sha256']
    assert dep['resources']==receipt['resources']
    assert dep['source_sha256']==row['source_sha256']==row['source_copy_sha256']==row['remote_R57_source_hash']
    source_path=replay_root/dep['source_snapshot']
    assert source_path.is_file() and sha(source_path)==dep['source_sha256']
    assert len(dep['complete_print_axioms'])>0
    dep_log=(replay_root/row['log']).read_text()
    assert f'Maximum resident set size (kbytes): {row["peak_rss_kib"]}' in dep_log
    assert 'Swaps: 0' in dep_log and 'Exit status: 0' in dep_log
    assert f'Elapsed (wall clock) time' in dep_log
    for line in dep['complete_print_axioms']:
        assert line in dep_log, f"missing dependency axiom report in {row['log']}: {line}"
        report_axioms(line)
    assert dep['complete_print_axioms']==row['complete_print_axioms']
    assert dep['wall_time']==row['wall_time'] and dep['peak_rss_kib']==row['peak_rss_kib']
    total_dependency_reports += len(dep['complete_print_axioms'])
assert total_dependency_reports==57
# Check the successful direct imported object hashes against the saved initial dependency inventory.
for module,digest in receipt['direct_local_import_sha256'].items():
    matches=[m for m in cache['minimal_transitive_local_module_graph'] if m.get('module')==module]
    assert matches and matches[0].get('source_sha256')==digest, f'direct import source mismatch or absent from cache graph: {module}'
# All required attempt and cache evidence is present; checker does not interpret theorem semantics.
required=['attempts/01-missing-cache/source.lean','attempts/01-missing-cache/lean.log','attempts/01-missing-cache/receipt.json','attempts/02-successful/source.lean','attempts/02-successful/lean.log','attempts/02-successful/receipt.json','runner/run_focus.py','proof-route/LEAD_PROOF_ROUTE.md']
for rel in required: assert (ROOT/rel).is_file(), rel
print(json.dumps({'status':'PASS','package_files':len(package_files),'successful_target_source_sha256':sha(production),'successful_target_exit':receipt['exit_status'],'initial_cache_failure_exit':failed['exit_status'],'dependency_replay':{'objects':replay['compiled_dependency_count'],'axiom_reports':total_dependency_reports,'all_exit_zero':replay['all_exit_zero'],'all_swap_zero':replay['all_swap_zero']},'compiled_artifacts_in_bundle':0,'scratch_required':False,'scratch_ignored_mode':ignore_scratch,'Lean_rerun':False},indent=2))
