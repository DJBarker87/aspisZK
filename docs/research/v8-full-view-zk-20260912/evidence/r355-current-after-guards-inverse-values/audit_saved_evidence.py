#!/usr/bin/env python3
"""Read-only portable consistency check for saved R355 compile evidence."""
from pathlib import Path
import hashlib, json, re, subprocess
HERE = Path(__file__).resolve().parent
REPO = Path(__file__).resolve().parents[5]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((HERE/'manifest.json').read_text());r=json.loads((HERE/'compile-receipt.json').read_text());p=json.loads((HERE/'release-provenance.json').read_text())
s=HERE/'source/R355AfterGuardsInverseValues.lean';snap=HERE/'source/R355AfterGuardsInverseValues.compile-snapshot.lean'
assert sha(s)==sha(snap)==m['source_sha256']==r['source_sha256']==p['compile_source_snapshot_sha256']
imports={'AspisV8R19.R353AfterGuardsCriterion':HERE/'imports/AspisV8R19_R353AfterGuardsCriterion.lean','AspisV8R19.R354ReverseInverseModel':HERE/'imports/AspisV8R19_R354ReverseInverseModel.lean'}
assert set(re.findall(r'^import\s+([A-Za-z0-9_.]+)',s.read_text(),re.M))==set(imports)==set(r['direct_local_import_sha256'])
for name,path in imports.items():assert sha(path)==r['direct_local_import_sha256'][name]==p['direct_local_imports'][name]['sha256']
axioms=(HERE/'axioms.txt').read_text().strip();log=(HERE/'logs/aspis-focus-1790941458038543000.log').read_text()
assert axioms in log and 'sorryAx' not in axioms and m['complete_print_axioms']==r['complete_print_axioms'] and len(m['complete_print_axioms'])==3
assert m['exit_status']==r['exit_status']==0 and m['wall_time']==r['wall_time']=='0:01.54' and m['peak_rss_kib']==r['peak_rss_kib']==3710348 and m['swaps']==r['swaps']==0
for key in ('MemoryHigh','MemoryMax','MemorySwapMax','TasksMax'):assert m['resources'][key]==r['resources'][key]
assert m['resources']['flags']==r['resources']['lean_flags']
assert json.loads((HERE/'history-index.json').read_text())['failed_candidate_count']==0
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip();rev=r['source_revision'];assert rev==p['compile_campaign_revision'];assert subprocess.run(['git','merge-base','--is-ancestor',rev,head],cwd=REPO).returncode==0;assert p['current_HEAD_equality_required'] is False
g=json.loads((HERE/'local-import-graph.json').read_text());assert g['acyclic'] and g['cycle_count']==0
for rel,h in json.loads((HERE/'SHA256SUMS.json').read_text()).items():assert (HERE/rel).is_file() and sha(HERE/rel)==h,rel
print(json.dumps({'overall':'PASS','compile_revision':rev,'audit_head':head,'source_sha256':sha(s),'direct_imports':len(imports),'graph_nodes':g['node_count'],'graph_edges':g['edge_count'],'failed_history_runs':0,'axiom_reports':len(m['complete_print_axioms'])}))
