"""Offline final-source/receipt/graph preflight. Never launches Lean or mutates host."""
from pathlib import Path
import hashlib, json, re, lzma, subprocess
E=Path(__file__).resolve().parent
R=E.parents[1]
def read(name): return json.loads((E/name).read_text())
def sha(data): return hashlib.sha256(data).hexdigest()
verification=read('NDR_VERIFICATION.json')
packaging=read('NDR_AGGREGATION_PACKAGING.json')
blocked={r['module'] for r in packaging['bodies']}
assert set(verification['missing_modules'])==blocked
assert verification['passing_modules']==verification['planned_modules']-len(blocked)
assert not (E/'NDR_A001.json').exists(), 'Final compile reserved already; recover only'
source=(R/'lean/NDR_CombinedAudit.lean').read_text()
assert sha(source.encode())==packaging['source_sha256']
for row in packaging['bodies']:
    original=(R/'lean'/(row['module']+'.lean')).read_text()
    assert sha(original.encode())==row['source_sha256']
    body=''.join(line for line in original.splitlines(keepends=True) if not line.startswith('import '))
    embedded=source.split('-- BEGIN verbatim body from '+row['module']+'.lean\n',1)[1].split('\n-- END verbatim body from '+row['module']+'.lean\n',1)[0]
    assert body==embedded and sha(body.encode())==row['verbatim_body_sha256']
    code=re.sub(r'/\-.*?\-/|--[^\n]*','',body,flags=re.S)
    assert not re.search(r'\b(?:rfl|decide|norm_num|unfold)\b',code),row['module']
for row in read('NDR_SOURCE_PINS.json'):
    assert sha((R/'lean'/(row['module']+'.lean')).read_bytes())==row['sha256']
for attempt in ['NDR_L003','NDR_L004']:
    receipt=read(attempt+'/receipt.json')
    assert receipt['exit_status']==0 and str(receipt['swaps'])=='0'
    for line in receipt['print_axioms']:
        match=re.search(r'depends on axioms: \[([^]]*)\]',line)
        if match: assert set(match[1].split(', '))<={'propext','Classical.choice','Quot.sound'}
objects=read('NDR_REBUILT_OBJECT_PINS.json')
assert objects['standalone_plan_modules']==verification['passing_modules']
assert len(objects['entries'])==verification['passing_modules']+4
for stem in ['NDR_ATTEMPTS_full_through_B024.jsonl','NDR_BUILD_RECEIPTS_full_through_B020.json']:
    assert sha(lzma.decompress((E/(stem+'.xz')).read_bytes()))==(E/(stem+'.sha256')).read_text().split()[0]
seed=json.loads((E.parent/'native-reconcile-20261028/NDO_SEED_PINS.json').read_text())
graph={r['module']:r['imports'] for r in seed['objects']}
def imports(text): return [m for line in re.findall(r'^import\s+([^\n]+)',text,re.M) for m in line.split()]
for row in read('NDR_SOURCE_PINS.json'):
    graph[row['module']]=imports((R/'lean'/(row['module']+'.lean')).read_text())
for m in ['NDO_InstalledIdentity','NDO_PhaseIdentity','NDR_HeadlineNatives']:
    graph[m]=imports((R/'lean'/(m+'.lean')).read_text())
pending=imports(source)
seen=set()
while pending:
    m=pending.pop()
    if m in seen: continue
    assert m in graph,('missing static dependency graph node',m)
    seen.add(m);pending.extend(graph[m])
assert not seen&blocked
provenance=read('NDR_PROVENANCE.json')
assert len(provenance['entries'])==76
assert all(row['historical'] not in seen for row in provenance['entries'])
(E/'NDR_FINAL_IMPORT_PLAN.json').write_text(json.dumps(sorted(seen),indent=2)+'\n')
result=dict(status='READY for sole final aggregation; runner hashes and admission still require fresh checks',
            source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
            final_source_sha256=sha(source.encode()),standalone_passed=verification['passing_modules'],
            standalone_missing=sorted(blocked),verbatim_aggregation_bodies=len(blocked),
            predicted_import_modules=len(seen),historical_gaps_statically_excluded=76,
            object_pin_manifest_sha256=sha((E/'NDR_REBUILT_OBJECT_PINS.json').read_bytes()),
            focused_identities_and_canonical_axiom_audit_pass=True,
            large_reduction_tokens_in_consolidated_bodies=False,
            next_consumer='NDR_CombinedAudit: JHx_Instance tree certificates -> exact joint source -> sourceOnHeadline and two-root axioms/constant audit',
            packaging_limit='Not all 3118 standalone normal-cap modules pass; the five documented thin bodies are compiled in the final source instead of a strict NDO_Joint import.')
(E/'NDR_FINAL_PREFLIGHT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
