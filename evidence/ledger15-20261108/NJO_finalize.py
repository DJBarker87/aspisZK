from pathlib import Path
import json,lzma,hashlib,collections,subprocess,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def put(n,x):
 raw=(json.dumps(x,indent=1,sort_keys=True)+'\n').encode();p=E/n
 if len(raw)>20_000_000 or n=='NJO_LEDGER.json':
  Path(str(p)+'.xz').write_bytes(lzma.compress(raw,preset=6));Path(str(p)+'.sha256').write_text(H(raw)+'\n');p.unlink(missing_ok=True)
 else:p.write_bytes(raw)
required=J(E/'NJO_AUDIT_ROOTS.json')['roots'];results=[];disagreements=[];nonzero=[]
for i in range(30):
 d=J(E/f'NJO_audit/batch{i}/proof{i}.json');results+=d['results']
 if d['exit_status']:nonzero.append(f'NJO_L{i+9:03}')
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},r['root']
  if not r['equal']:disagreements.append(dict(batch=i,**r))
assert len(results)==len(required)==len({r['root']for r in results})and{r['root']for r in results}==set(required)
assert[r['root']for r in disagreements]==['NHC_DecodeModel.decoder_error']
fx=J(E/'NJO_audit/fixtures/fixtures.json');oldfx=J(E.parent/'ledger14-20261108/NJK_audit/fixtures/fixtures.json');assert fx['exit_status']==0 and fx['results']==oldfx['results']and len(fx['results'])==8
scan=[json.loads(l)for l in(E/'NJO_LOADED_scan.jsonl').read_text().splitlines()];assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
assert J(E/'NJO_audit/scan/scan.json')['exit_status']==0
put('NJO_SCAN.json',dict(exit_status=0,modules=len(scan),declarations=sum(r['declarations']for r in scan),references=sum(r['edges']for r in scan),dangling=0,incompatible_owners=0,import_mismatches=0,compatible_cached_replicas=sum(len(r['cached_replicas'])for r in scan),scanner='NFX method; NIU_Driver module/root/path-only adaptation',attempt='NJO_L008',full_combined_import='NJO_COMBINED_IMPORT',canonical_duplicate_owners=0))
rs=[json.loads(l)for l in(E/'NJO_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rs)==40 and len({r['attempt']for r in rs})==40
assert rs[-1]['attempt']=='NJO_L040'and rs[-1]['exit_status']==0
for r in rs:
 a=r['attempt'];ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 rc=J(E/a/'receipt.json');assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(rc['swaps'])=='0'and rc['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-ledger15-20261108/NJO_target'
 assert r['exit_status']==0 or a in nonzero
resources=dict(scopes=len(rs),kinds=dict(collections.Counter(r['kind']for r in rs)),wall_seconds=sum(r['wall_seconds']for r in rs),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rs),swaps=sum(int(r['swaps'])for r in rs),retained_tool_nonzero_exits=[dict(attempt=r['attempt'],target=r['module'],exit=r['exit_status'])for r in rs if r['exit_status']],kani=0,extraction=0,aggregation16G_scopes=0)
binary=J(E/'NJO_L006/NJO_ProofDriver_BINARY_PIN.json')['sha256']
for r in rs:
 p=E/r['attempt']/'NJO_ProofDriver_BINARY_PIN.json'
 if p.exists():assert J(p)['sha256']==binary
oldAudit=J(E.parent/'ledger14-20261108/NJK_AUDIT.json');canonical=subprocess.check_output(['git','show','HEAD:evidence/axaudit2-20261102/NEP_WALKER.lean'],cwd=R);assert H(canonical)==oldAudit['walker']['sha256'];(E/'NJO_WALKER_SOURCE.lean.txt').write_bytes(canonical)
sel=J(E/'NJO_L004/receipt.json')['deps_fingerprint']['selected_objects'];actual=[v for k,v in sel.items()if k.endswith('/NFA_WALKER.olean')];assert len(actual)==1 and actual[0]['sha256']==oldAudit['walker']['object_pins'][0]['sha256']
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:assert(E/'NJO_L006/sources/NJO_native'/n).read_bytes()==(E.parent/'ledger14-20261108/NJK_L006/sources/NJK_native'/n).read_bytes()
put('NJO_AUDIT.json',dict(status='PASS_REQUIRED_RAW_ROOTS_WITH_RETAINED_TOOL_FINDING',full_composition_pass=True,combined='NJO_COMBINED_IMPORT',combined_attempt='NJO_L001',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(required),all_required_raw_roots_present=True,raw_standard_axioms_only=True,axioms=sorted({a for r in results for a in r['walked_axioms']}),collect_axioms_disagreements=disagreements,raw_authoritative_ruling="(ab')(3)",retained_nonzero_audit_exits=nonzero,same_optimized_proof_binary_sha256=binary,fixtures=fx['results'],scanner='NJO_SCAN.json',walker=dict(canonical='evidence/axaudit2-20261102/NEP_WALKER.lean',source='NJO_WALKER_SOURCE.lean.txt',byte_identical=True,sha256=H(canonical),object_pins=actual,driver_diffs=['NJO_Driver.diff','NJO_ProofDriver.diff'],native_link_inputs_byte_identical_to_NIU=True),resources=resources,security_target_established=False,cold_release_replay=False))
put('NJO_RESOURCES.json',resources)
assert J(E/'NJO_PREDECESSOR_COMPARISON.json')['status']=='PASS'
import copy
for pre in ['NJE','NJB']:assert J(E/f'NJO_{pre}_REVALIDATION.json')['status']=='PASS'
review=J(E/'NJO_CANDIDATE_REVIEW.json');assert len(review['rows'])==25 and review['no_double_count']
assert J(E/'NJO_L039/receipt.json')['exit_status']==0
basis=J(E.parent/'ledger14-20261108/NJK_LEDGER.json.xz');ledger=copy.deepcopy(basis);oldby={r['row']:r for r in basis['rows']};by={r['row']:r for r in ledger['rows']};changes=[]
for c in review['rows']:
 r=by[c['row']];assert r['status']=='OPEN' and r['obligation_statement_hash']==c['basis_obligation_statement_hash']
 o=copy.deepcopy(r['obligation']);o['basis_obligation']=r['obligation'];o['certificate']=c['certificate'];o['kernel_roots']=c['kernel_statements'];o['NJO_complete_clause_review']=c['original_clauses'];o['NJO_hypothesis_inventory']=c['hypothesis_inventory'];o['NJO_root_domain']=c['root_domain'];o['NJO_semantic_review']=c['review']
 r.update(previous_status='OPEN',status='CLOSED',obligation=o,obligation_statement_hash=H(json.dumps(o,sort_keys=True,separators=(',',':')).encode()),owner_module=c['kernel_statements'][0]['owner_module'],owner_role='canonical checked row packet',root_owners=[dict(root=x['root'],owner_module=x['owner_module'],obligation_statement_sha256=H(x['obligation_statement'].encode()))for x in c['kernel_statements']],evidence_dir='evidence/ledger15-20261108')
 changes.append(dict(row=r['row'],provider=c['provider'],previous_status='OPEN',status='CLOSED',primary_root=r['root_owners'][0]['root'],owner_module=r['owner_module'],basis_obligation_statement_hash=c['basis_obligation_statement_hash'],complete_obligation_statement_hash=r['obligation_statement_hash'],domain=c['root_domain'],roots=r['root_owners'],caller_clauses='All original clauses retained verbatim; NJO_PARENT_CLAUSES.json additionally exposes multiproof unit obligations at the OPEN verify_in_place caller'))
parent=J(E/'NJO_PARENT_CLAUSES.json')
for rid in parent['parents']:
 r=by[rid];assert r['status']=='OPEN';o=r['obligation'];o['NJO_basis_obligation']=copy.deepcopy(oldby[rid]['obligation']);o['NJO_parent_unit_clauses']=[c for c in parent['clauses']if c['parent']==rid]
 o['caller_domain_obligations'] += [c['caller_clause']for c in parent['clauses']if c['parent']==rid]
 r['obligation_statement_hash']=H(json.dumps(o,sort_keys=True,separators=(',',':')).encode())
 assert all(c['caller_clause']['status']=='OPEN'for c in parent['clauses']if c['parent']==rid)
counts=dict(collections.Counter(r['status']for r in ledger['rows']));assert counts=={'CLOSED':463,'OPEN':136};assert ledger['trust_rows']==basis['trust_rows']
ledger.update(basis='NJK ledger14 plus25 NJO-gated NJE/NJB occurrences; explicit retained unit caller clauses on OPEN verify_in_place',basis_delta='NJO_LEDGER_DELTA.json',counts=counts,gate='PASS',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),security_target_established=False)
put('NJO_LEDGER.json',ledger)
put('NJO_LEDGER_DELTA.json',dict(schema_version=1,basis='evidence/ledger14-20261108/NJK_LEDGER.json.xz',before=dict(CLOSED=438,QUALIFIED=0,OPEN=161),after=dict(CLOSED=463,QUALIFIED=0,OPEN=136),new_closed_rows=[c['row']for c in changes],new_count=25,rows=changes,no_double_count=True,no_other_status_change=True,gate=[r['attempt']for r in rs],explicit_open_parent_clause_updates=parent,trust_rows_changed=False,security_target_established=False,supporting_imports_without_credit=['NJG','NJA'],rejected_candidates=[]))
review['status']='PASS_COMPLETE_STATEMENTS_OWNERS_AND_FULL_GATE';review['gate_pass']=True;put('NJO_CANDIDATE_REVIEW.json',review)
from NJO_report import report
report(ledger,resources)
print(json.dumps(dict(status='PASS',closed=463,open=136,qualified=0,roots=len(required),modules=len(scan),scopes=len(rs))))
