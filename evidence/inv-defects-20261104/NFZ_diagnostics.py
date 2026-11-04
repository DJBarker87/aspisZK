"""Compile-free diagnostics on the retained failing preflight and proposed edges."""
from pathlib import Path
import json,lzma,hashlib,subprocess,collections
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def put(n,v):(E/n).write_text(json.dumps(v,indent=1)+'\n')
g=json.loads((E/'NFZ_GRAPH_CHECK.json').read_text());m=json.loads(lzma.open(E/'NFZ_METADATA.json.xz').read()) if (E/'NFZ_METADATA.json.xz').exists() else json.loads((E/'NFZ_METADATA.json').read_text());f=json.loads(lzma.open(E/'NFZ_FROZEN_SOURCE.json.xz').read())
missing={tuple(x) for x in g['missing']};allowed={('aspis-r1-cert-build','0.0.0',None),('aspis-r1-cert-check','0.0.0',None),('aspis-z4b-probe','0.1.0',None)}
assert missing==allowed and not g['added'] and not g['edge_errors']
assert all('r1p-check' not in n['features'] for n in m['resolve']['nodes'])
put('NFZ_PREFLIGHT_DIAGNOSIS.json',dict(original_verdict=g['graph_matches_frozen'],reason='Own preflight required equality with every lockfile package, including disabled optional local packages; no compilation started',exact_missing=g['missing'],added=g['added'],edge_errors=g['edge_errors'],same_projection_as='evidence/slice-d-define-20261104/NFQ_gate.py',frozen_lock_sha256=hashlib.sha256(f['Cargo.lock'].encode()).hexdigest(),metadata_projection_pass=True,not_a_new_build_or_compiler_result=True,script_repair='NFZ_check.py corrected, original exact source retained in NFZ_B001/sources/NFZ_check.py; no new scope or rerun'))
# The exact compiler versions are read-only queries, not a Rust compilation.
code="""from pathlib import Path
import subprocess,json,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-inv-defects-20261104');result={}
for tool in ['rustc','cargo']:
 r=subprocess.run(['/home/dombarker/.cargo/bin/'+tool,'+nightly-2026-09-17','-Vv'],text=True,capture_output=True);result[tool]=dict(exit=r.returncode,text=r.stdout+r.stderr)
result['frozen_lock_after']=hashlib.sha256((b/'NFZ_src/Cargo.lock').read_bytes()).hexdigest();result['target_created']=(b/'NFZ_target').exists();result['MIR_files']=[p.name for p in b.glob('*.mir')];result['runner_sha256']=hashlib.sha256((b/'S2W_run_host.py').read_bytes()).hexdigest()
print(json.dumps(result))
"""
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
v=json.loads(r.stdout);assert v['frozen_lock_after']==g['lock_sha256'] and not v['target_created'] and not v['MIR_files'];put('NFZ_TOOLS_AND_LOCK.json',v)
scan=json.loads((E/'NFZ_SCAN.json').read_text());c=json.loads((E/'NFZ_CANDIDATES.json').read_text())
proposed=[]
for x in c['candidates']:
 if x['to'] in ['crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31','programs/r1-cost-probe/src/lib.rs::error']:
  if x['caller'].endswith('::process_r1_cost_probe_instruction'):continue # inactive legacy cfg
  edge=dict(from_function=x['caller'],to=x['to'],kind=x['kind'],evidence='NFZ_SCAN.json',status='PROPOSED_SOURCE_ONLY_NOT_REVIEWED')
  edge['from']=edge.pop('from_function')
  if edge not in proposed:proposed.append(edge)
put('NFZ_PROPOSED_EDGES.json',proposed)
L=json.loads(lzma.open(R/'evidence/ledger7-20261104/NFX_LEDGER.json.xz').read());graph=collections.defaultdict(set)
for r in L['rows']:graph[r['function']].update(r['canonical_callees'])
for x in proposed:graph[x['from']].add(x['to'])
root='programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction';seen={root};q=collections.deque([root])
while q:
 for t in graph[q.popleft()]:
  if t not in seen:seen.add(t);q.append(t)
S=json.loads((R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json').read_text());qs=set(S['slices']['Q']['functions'])|set(S['slices']['S']['functions']);D=seen-qs
hyp=dict(authority='HYPOTHETICAL source-discovery edges, not admitted; omits pending new-node expansion',proposed_edges=proposed,covered_existing_rows=sum(r['function'] in seen|qs for r in L['rows']),total_existing_rows=len(L['rows']),D_functions=len(D),D_rows=sum(r['function'] in D for r in L['rows']),D_edges=sum(t in D for f in D for t in graph[f]),outside=[r['row'] for r in L['rows'] if r['function'] not in seen|qs],unreviewed_new_function_candidates=scan['new_function_candidates'])
# Recomputing Q/S roots under even this incomplete overlay changes Q.
# Hence NFQ's exact-original-slice assertion would refuse an admitted overlay.
def closure(roots):
 seen=set(roots);q=collections.deque(roots)
 while q:
  for t in graph[q.popleft()]:
   if t not in seen:seen.add(t);q.append(t)
 return seen
hyp['slice_root_closure_growth']={name:sorted(closure(spec['roots'])-set(spec['functions'])) for name,spec in S['slices'].items()}
hyp['original_NFQ_slice_assertion_would_pass']=not any(hyp['slice_root_closure_growth'].values())
hyp['D_counts_use_original_fixed_QS_membership']=True
put('NFZ_HYPOTHETICAL_COVERAGE.json',hyp)
put('NFZ_LEDGER_DELTA.json',dict(frozen_revision=L['frozen_revision'],baseline='evidence/ledger7-20261104/NFX_LEDGER.json.xz',baseline_sha256=sha(R/'evidence/ledger7-20261104/NFX_LEDGER.json.xz'),overlay='NFZ_OVERLAY.json',admitted_edges=[],new_rows=[],removed_rows=[],reachability_excluded_rows=[],new_closed_rows=[],status_changes=[],before=L['coverage'],after=L['coverage'],slice_union_before=dict(covered=585,total=587),slice_union_after=dict(covered=585,total=587),target_rows=[dict(row=r,function=next(x['function'] for x in L['rows'] if x['row']==r),before='OPEN',after='OPEN',slices_before=[],slices_after=[],blocking='missing compiler review') for r in ['TX2:046','TX2:211']],hypothetical_existing_row_only=hyp))
print(json.dumps(dict(projected_metadata_graph=True,hypothetical=hyp)))
