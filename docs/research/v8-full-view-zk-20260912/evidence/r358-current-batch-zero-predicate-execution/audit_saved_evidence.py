#!/usr/bin/env python3
"""Read-only portable consistency checker for R358 saved compile evidence."""
from pathlib import Path
import hashlib, json, re, subprocess
HERE=Path(__file__).resolve().parent
REPO=Path(__file__).resolve().parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((HERE/'manifest.json').read_text());r=json.loads((HERE/'compile-receipt.json').read_text());p=json.loads((HERE/'release-provenance.json').read_text())
s=HERE/'source/R358BatchZeroPredicate.lean';snap=HERE/'source/R358BatchZeroPredicate.compile-snapshot.lean'
assert sha(s)==sha(snap)==m['source_sha256']==r['source_sha256']==p['compile_source_snapshot_sha256']=='4feca9a7cbc3e4ec09052ee2caa0a3ca98c63ba28930ce194298990fa3cc4500'
imports={'AspisR357BatchZeroPredicateRaw':HERE/'imports/AspisR357BatchZeroPredicateRaw.lean','AspisV8R19.ComplexBaseExecution':HERE/'imports/AspisV8R19_ComplexBaseExecution.lean'}
assert set(re.findall(r'^import\s+([A-Za-z0-9_.]+)',s.read_text(),re.M))==set(imports)
for name,path in imports.items():assert sha(path)==r['direct_local_import_sha256'][name]==p['direct_local_imports'][name]['sha256']
axioms=(HERE/'axioms.txt').read_text().strip();log=(HERE/'logs/aspis-focus-1790942076751856000.log').read_text()
assert axioms in log and m['complete_print_axioms']==r['complete_print_axioms'] and len(m['complete_print_axioms'])==6 and 'sorryAx' not in axioms
assert m['exit_status']==r['exit_status']==0 and m['wall_time']==r['wall_time']=='0:01.41' and m['peak_rss_kib']==r['peak_rss_kib']==3700688 and m['swaps']==r['swaps']==0
for key in ('MemoryHigh','MemoryMax','MemorySwapMax','TasksMax'):assert m['resources'][key]==r['resources'][key]
assert m['resources']['flags']==r['resources']['lean_flags']
h=HERE/'history/1790942031916614000';hr=json.loads((h/'receipt.json').read_text());assert sha(h/'source.lean')==hr['source_sha256'] and hr['exit_status']==1 and 'sorryAx' in ' '.join(hr['complete_print_axioms']) and 'Exit status: 1' in (h/'compile.log').read_text()
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip();rev=r['source_revision'];assert rev==p['compile_campaign_revision'];assert subprocess.run(['git','merge-base','--is-ancestor',rev,head],cwd=REPO).returncode==0;assert p['current_HEAD_equality_required'] is False
g=json.loads((HERE/'local-import-graph.json').read_text());assert g['acyclic'] and g['cycle_count']==0
for rel,hsh in json.loads((HERE/'SHA256SUMS.json').read_text()).items():assert (HERE/rel).is_file() and sha(HERE/rel)==hsh,rel
print(json.dumps({'overall':'PASS','compile_revision':rev,'audit_head':head,'source_sha256':sha(s),'direct_imports':len(imports),'graph_nodes':g['node_count'],'graph_edges':g['edge_count'],'failed_history_runs':1,'axiom_reports':len(m['complete_print_axioms'])}))
