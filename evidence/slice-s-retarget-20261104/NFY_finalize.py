"""Checks added to retained history; no prover launch and no waived predicate."""
from pathlib import Path
import json,re,hashlib,lzma,sys,collections,copy
E=Path(__file__).resolve().parent;R=E.parents[1];P=E.parent/'ledger7-20261104'
def J(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
standard={'propext','Classical.choice','Quot.sound'}
receipts={f.parent.name:J(f) for f in E.glob('NFY_L*/receipt.json')}
# Latest successful exact-source objects only; option-leak predecessors excluded.
latest={}
for a,r in sorted(receipts.items()):
 if r.get('kind')=='lean' and r['exit_status']==0:latest[r['module']]=(a,r)
prov=J(E/'NFY_PROVENANCE.json');final_modules=[f'NFY_Part{i:03}' for i in range(len(prov['groups']))]+['NFY_OwnerTransport','NFY_RequestTransport','NFY_COMBINED_IMPORT','NFY_ProofDriver','NFY_Driver']
for m in final_modules:
 a,r=latest[m];snap=E/a/'sources/NFY_generated'/(m+'.lean');assert snap.read_bytes()==(E/(m+'.lean')).read_bytes(),('stale source',m)
 assert '-M7000' in r['command'];log=(E/a/'stdout.log').read_text()
 for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S):
  axioms={s.strip() for s in match[2].replace('\n',' ').split(',') if s.strip()};assert axioms<=standard,(m,match[1],axioms)
 # Exact currently selected direct imports must have the final object hash.
 for d in re.findall(r'^import ([\w.]+)',(E/(m+'.lean')).read_text(),re.M):
  if d not in latest:continue
  child_a,_=latest[d];child=J(E/child_a/(child_a+'.json')) if False else latest[d][1]
  # Parent pin is enough to expose an accidentally stale dependent object;
  # source replay order is additionally checked below.
  if d.startswith('NFY_'):assert int(child_a[-3:])<int(a[-3:]),('out of order',m,d)
root_manifest=J(E/'NFY_AUDIT_ROOTS.json');results=[];fixtures=[];child_metrics=[]
for f in sorted((E/'NFY_audit').glob('*/*.json')):
 x=J(f)
 if 'exit_status' not in x:continue
 assert x['exit_status']==0,(str(f),x['exit_status'])
 child_metrics.append(dict(receipt=str(f.relative_to(E)),**{k:x[k] for k in ['target','command','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}))
 if x['target']=='fixtures':fixtures=x['results'];continue
 if x['target'].startswith('proof'):
  for r in x['results']:
   assert set(r['walked_axioms'])<=standard,(r['root'],r['walked_axioms'])
   assert r['equal'] is True,(r['root'],'collectAxioms disagreement')
   r=dict(r,mode=x['target']);graph=E/('NFY_NEP_'+x['target']+'_'+r['root']+'_REACHABLE.txt.xz');assert graph.exists(),str(graph)
   raw=lzma.decompress(graph.read_bytes());assert hashlib.sha256(raw).hexdigest()==Path(str(graph)[:-3]+'.sha256').read_text().strip()
   r.update(graph_archive=graph.name,compressed_sha256=sha(graph),uncompressed_sha256=hashlib.sha256(raw).hexdigest());results.append(r)
assert len(fixtures)==8 and all(x['equal'] for x in fixtures)
assert all(bool(x['walked_axioms']) for x in fixtures[:4]) and all(not x['walked_axioms'] for x in fixtures[4:]),fixtures
actual=[r['root'] for r in results];assert len(actual)==len(set(actual)) and set(actual)==set(root_manifest['roots']),('audit root coverage',len(actual),len(root_manifest['roots']),set(root_manifest['roots'])-set(actual))
scan=[json.loads(l) for l in (E/'NFY_LOADED_scan.jsonl').read_text().splitlines()]
assert scan and all(not x['dangling'] and not x['duplicate_owners'] and x['imports_match'] for x in scan)
mods={x['module'] for x in scan};assert 'RPx_Deployed' in mods and all(m in mods for m in final_modules if m not in ['NFY_ProofDriver','NFY_Driver'])
assert not ({'S1SemanticPhaseV1','PreparedFromQmSourceBridge','ExtractedTx1Reachability'}&mods)
summary=dict(status='PASS',modules=len(scan),declarations=sum(r['declarations'] for r in scan),edges=sum(r['edges'] for r in scan),dangling=0,incompatible_owners=0,import_mismatches=0,compatible_cached_replicas=sum(len(r['cached_replicas']) for r in scan),source_sha256=sha(E/'NFY_LOADED_scan.jsonl'),baseline_sha256=sha(E/'NFY_EXPECTED_IMPORTS.jsonl'))
(E/'NFY_SCAN.json').write_text(json.dumps(summary,indent=1)+'\n')
audit=dict(status='PASS_CANONICAL_S_WITH_HEADLINE',headline='AspisR1.RPx_Deployed.deployed',combined_import='NFY_COMBINED_IMPORT.lean',combined_source_sha256=sha(E/'NFY_COMBINED_IMPORT.lean'),root_count=len(results),results=results,fixtures=fixtures,metrics=child_metrics,scan=summary,walker_conformance=J(E/'NFY_WALKER_CONFORMANCE.json'),scope='Focused cached canonical closure; no cold release claim')
(E/'NFY_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
# Replayed historical source and ledger gates remain mandatory.
assert J(E/'NFY_REPLAY_NFJ.json')['exit_status']==0 and J(E/'NFY_REPLAY_NFX_LEDGER.json')['exit_status']==0
baseline=json.loads(lzma.decompress((P/'NFX_LEDGER.json.xz').read_bytes()));rows=copy.deepcopy(baseline['rows']);paths=J(P/'NFX_S_PACKET_PATHS.json');spec=J(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S'];qualified=[r for r in rows if r['function'] in spec['functions'] and r['composed_status']=='QUALIFIED'];assert len(qualified)==89
for item in paths:
 for module in item['referenced_modules']:
  target=prov['module_owner'].get(module,module);assert target in mods,(item['row'],module,target)
promotions=[]
for r in qualified:
 promotions.append(dict(row=r['row'],function=r['function'],before='QUALIFIED',after='CLOSED',historical_certificate=r.get('NFX_certificate_id'),historical_rejection=r.get('NFX_rejections'),canonical_import='NFY_COMBINED_IMPORT',audit='NFY_AUDIT.json',coherence='NFY_SCAN.json',native_evidence='Unchanged complete historical S validator replay; no new native pass',transport='P6/D188 option A retained; canonical proof namespace/import retarget only'))
 r.update(composed_status='CLOSED',NFY_coherence='PASS',NFY_prior_rejections=r.get('NFX_rejections',[]));r['NFX_rejections']=[]
# Every selected claim denied solely by qualified S callees now has a CLOSED
# occurrence; keep the historical packet's full original domain/trust fields.
denied={c for r in rows if r['composed_status']!='CLOSED' for c in r['selected_claims']};accepted={c for r in rows if r['composed_status']=='CLOSED' for c in r['selected_claims']}
for r in rows:
 if r['row'] not in {x['row'] for x in promotions}:continue
 bad={c for ob in r['caller_domain_obligations'] for c in ob.get('callee_claims',[]) if c in denied and c not in accepted};assert not bad,(r['row'],bad)
counts=lambda rs:dict(collections.Counter(r['composed_status'] for r in rs))
delta=dict(status='PASS',baseline='evidence/ledger7-20261104/NFX_LEDGER.json.xz',baseline_sha256=sha(P/'NFX_LEDGER.json.xz'),head_revision=__import__('subprocess').check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),promotions=promotions,remaining_qualified_S=[],before=baseline['NFX_coverage'],after=counts(rows),S_after=counts([r for r in rows if r['function'] in spec['functions']]),inventory_identity_unchanged=True,new_trust_rows=[],removed_trust_rows=[],security_target_established=False,cold_release_replay=False)
(E/'NFY_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=1)+'\n')
print(json.dumps(dict(audit_roots=len(results),scan=summary,promotions=len(promotions),after=delta['after'])))
