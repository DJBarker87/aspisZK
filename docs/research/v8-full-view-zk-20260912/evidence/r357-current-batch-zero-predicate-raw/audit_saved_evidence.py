#!/usr/bin/env python3
"""Read-only R357 evidence audit; never invokes Lean or the builder."""
from pathlib import Path
import hashlib, json, re, subprocess
HERE = Path(__file__).resolve().parent
REPO = Path(__file__).resolve().parents[5]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((HERE/'manifest.json').read_text());r=json.loads((HERE/'compile-receipt.json').read_text());p=json.loads((HERE/'release-provenance.json').read_text())
s=HERE/'source/AspisR357BatchZeroPredicateRaw.lean';snap=HERE/'source/AspisR357BatchZeroPredicateRaw.compile-snapshot.lean'
assert sha(s)==sha(snap)==m['source_sha256']==r['source_sha256']==p['compile_source_snapshot_sha256']=='65c6523618b88bd9130a28b535b566f291a5f3e89c87ea59c9b13e8e50be9156'
assert s.read_bytes()==(HERE/'staging-precompile/AspisR357BatchZeroPredicateRaw.lean').read_bytes()==(HERE/'staging-precompile/source/R357BatchZeroPredicateRaw.lean').read_bytes()
report=json.loads((HERE/'staging-precompile/provenance/raw-adapter.json').read_text());assert report['exact_copy']['replacement_count']==0 and report['output_sha256']==sha(s)
# Check each saved excerpt against the exact frozen R292 source line range, then verify ordered payload appears unchanged.
prov=HERE/'staging-precompile/provenance';ranges=report['selected_source_line_ranges_1_based_inclusive'];blocks=[]
for key,info in ranges.items():
 src=prov/('R292Types.input.lean' if info['source']=='types' else 'R292Funs.input.lean')
 actual=b''.join(src.read_bytes().splitlines(keepends=True)[info['first']-1:info['last']])
 excerpt=prov/f'{key}.excerpt.lean'
 assert actual==excerpt.read_bytes() and sha(excerpt)==info['byte_sha256'],key
 blocks.append(actual)
payload=b'\n'.join(blocks)
assert hashlib.sha256(payload).hexdigest()==report['exact_copy']['copied_payload_sha256']
assert s.read_bytes().count(payload)==1
assert (HERE/'source-block-audit.json').is_file()
# Local import copies are taken from the evidence bundle and match the runner receipt.
imports={'AspisR249R110Raw':HERE/'imports/AspisR249R110Raw.lean','AspisR278PrivateInverseRaw':HERE/'imports/AspisR278PrivateInverseRaw.lean'}
assert set(re.findall(r'^import\s+([A-Za-z0-9_.]+)',s.read_text(),re.M))=={'Aeneas.Std',*imports}
for name,path in imports.items():assert sha(path)==r['direct_local_import_sha256'][name]==p['direct_local_imports'][name]['sha256']
axioms=(HERE/'axioms.txt').read_text().strip();log=(HERE/'logs/aspis-focus-1790941965231802000.log').read_text()
assert axioms in log and m['complete_print_axioms']==r['complete_print_axioms'] and len(m['complete_print_axioms'])==6
assert 'sorryAx' not in axioms and m['exit_status']==r['exit_status']==0
assert m['wall_time']==r['wall_time']=='0:01.00' and m['peak_rss_kib']==r['peak_rss_kib']==2531080 and m['swaps']==r['swaps']==0
for key in ('MemoryHigh','MemoryMax','MemorySwapMax','TasksMax'):assert m['resources'][key]==r['resources'][key]
assert m['resources']['flags']==r['resources']['lean_flags']
assert json.loads((HERE/'history-index.json').read_text())['failed_candidate_count']==0
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip();rev=r['source_revision'];assert rev==p['compile_campaign_revision'];assert subprocess.run(['git','merge-base','--is-ancestor',rev,head],cwd=REPO).returncode==0;assert p['current_HEAD_equality_required'] is False
g=json.loads((HERE/'local-import-graph.json').read_text());assert g['acyclic'] and g['cycle_count']==0
for rel,h in json.loads((HERE/'SHA256SUMS.json').read_text()).items():assert (HERE/rel).is_file() and sha(HERE/rel)==h,rel
print(json.dumps({'overall':'PASS','compile_revision':rev,'audit_head':head,'source_sha256':sha(s),'source_blocks':len(blocks),'direct_imports':len(imports),'graph_nodes':g['node_count'],'graph_edges':g['edge_count'],'axiom_reports':len(m['complete_print_axioms'])}))
