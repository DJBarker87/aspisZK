#!/usr/bin/env python3
"""Verify the saved R366 formal evidence and byte-identical promoted source; no Lean invocation."""
from pathlib import Path
import hashlib, json

ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[4]
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''): h.update(block)
    return h.hexdigest()

def verify_sum_file(root, name='SHA256SUMS'):
    index=root/name
    files={p.relative_to(root).as_posix():p for p in root.rglob('*') if p.is_file() and p.name!=name}
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
package_files={p.relative_to(ROOT).as_posix():p for p in ROOT.rglob('*') if p.is_file() and p.name!='SHA256SUMS'}
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
# Check source copy graph hashes and copy edges, including the target outside the evidence directory.
graph=json.loads((ROOT/'copygraph.json').read_text())
for node in graph['nodes']:
    p=REPO/node['path']
    assert p.is_file() and sha(p)==node['sha256'], f'copygraph node mismatch: {node["path"]}'
for edge in graph['edges']:
    a=REPO/edge['from']; b=REPO/edge['to']
    assert a.is_file() and b.is_file() and sha(a)==sha(b), f'copygraph edge mismatch: {edge}'
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
# All required attempt and cache evidence is present; checker does not interpret theorem semantics.
required=['attempts/01-missing-cache/source.lean','attempts/01-missing-cache/lean.log','attempts/01-missing-cache/receipt.json','attempts/02-successful/source.lean','attempts/02-successful/lean.log','attempts/02-successful/receipt.json','runner/run_focus.py','proof-route/LEAD_PROOF_ROUTE.md']
for rel in required: assert (ROOT/rel).is_file(), rel
print(json.dumps({'status':'PASS','package_files':len(package_files),'successful_target_source_sha256':sha(production),'successful_target_exit':receipt['exit_status'],'initial_cache_failure_exit':failed['exit_status'],'dependency_replay':{'objects':replay['compiled_dependency_count'],'axiom_reports':report_count,'all_exit_zero':replay['all_exit_zero'],'all_swap_zero':replay['all_swap_zero']},'compiled_artifacts_in_bundle':0,'Lean_rerun':False},indent=2))
