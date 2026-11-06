from pathlib import Path
import json,lzma,hashlib,collections,subprocess,copy,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];P=E.parent/'ledger16-20261108';H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def put(n,x):
 raw=(json.dumps(x,indent=1,sort_keys=True)+'\n').encode();p=E/n
 if n=='NKC_LEDGER.json'or len(raw)>20_000_000:
  Path(str(p)+'.xz').write_bytes(lzma.compress(raw,preset=6));Path(str(p)+'.sha256').write_text(H(raw)+'\n');p.unlink(missing_ok=True)
 else:p.write_bytes(raw)
required=J(E/'NKC_AUDIT_ROOTS.json')['roots'];results=[];disagreements=[];nonzero=[]
for i in range(30):
 d=J(E/f'NKC_audit/batch{i}/proof{i}.json');results+=d['results']
 if d['exit_status']:nonzero.append(f'NKC_L{i+9:03}')
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},r['root']
  if not r['equal']:disagreements.append(dict(batch=i,**r))
assert len(results)==len(required)==len({r['root']for r in results})and{r['root']for r in results}==set(required)
assert[r['root']for r in disagreements]==['NHC_DecodeModel.decoder_error']
fx=J(E/'NKC_audit/fixtures/fixtures.json');oldfx=J(P/'NJW_audit/fixtures/fixtures.json');assert fx['exit_status']==0 and fx['results']==oldfx['results']and len(fx['results'])==8
scan=[json.loads(l)for l in(E/'NKC_LOADED_scan.jsonl').read_text().splitlines()];assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
assert J(E/'NKC_audit/scan/scan.json')['exit_status']==0
put('NKC_SCAN.json',dict(exit_status=0,modules=len(scan),declarations=sum(r['declarations']for r in scan),references=sum(r['edges']for r in scan),dangling=0,incompatible_owners=0,import_mismatches=0,compatible_cached_replicas=sum(len(r['cached_replicas'])for r in scan),scanner='NFX method; NJW_Driver module/root/path-only adaptation',attempt='NKC_L008',full_combined_import='NKC_COMBINED_IMPORT',canonical_duplicate_owners=0))
rs=[json.loads(l)for l in(E/'NKC_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rs)==40 and len({r['attempt']for r in rs})==40
assert rs[-1]['attempt']=='NKC_L040'and rs[-1]['exit_status']==0
for r in rs:
 a=r['attempt'];ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 rc=J(E/a/'receipt.json');assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(rc['swaps'])=='0'and rc['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-ledger17-20261108/NKC_target'
 assert r['exit_status']==0 or a in nonzero
resources=dict(scopes=len(rs),kinds=dict(collections.Counter(r['kind']for r in rs)),wall_seconds=sum(r['wall_seconds']for r in rs),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rs),swaps=sum(int(r['swaps'])for r in rs),retained_tool_nonzero_exits=[dict(attempt=r['attempt'],target=r['module'],exit=r['exit_status'])for r in rs if r['exit_status']],kani=0,extraction=0,aggregation16G_scopes=0)
binary=J(E/'NKC_L006/NKC_ProofDriver_BINARY_PIN.json')['sha256']
for r in rs:
 p=E/r['attempt']/'NKC_ProofDriver_BINARY_PIN.json'
 if p.exists():assert J(p)['sha256']==binary
oldAudit=J(P/'NJW_AUDIT.json');canonical=subprocess.check_output(['git','show','HEAD:evidence/axaudit2-20261102/NEP_WALKER.lean'],cwd=R);assert H(canonical)==oldAudit['walker']['sha256'];(E/'NKC_WALKER_SOURCE.lean.txt').write_bytes(canonical)
sel=J(E/'NKC_L004/receipt.json')['deps_fingerprint']['selected_objects'];actual=[v for k,v in sel.items()if k.endswith('/NFA_WALKER.olean')];assert len(actual)==1 and actual[0]['sha256']==oldAudit['walker']['object_pins'][0]['sha256']
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:assert(E/'NKC_L006/sources/NKC_native'/n).read_bytes()==(P/'NJW_L006/sources/NJW_native'/n).read_bytes()
put('NKC_AUDIT.json',dict(status='PASS_REQUIRED_RAW_ROOTS_WITH_RETAINED_TOOL_FINDING',full_composition_pass=True,combined='NKC_COMBINED_IMPORT',combined_attempt='NKC_L001',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(required),all_required_raw_roots_present=True,raw_standard_axioms_only=True,axioms=sorted({a for r in results for a in r['walked_axioms']}),collect_axioms_disagreements=disagreements,raw_authoritative_ruling="(ab')(3)",retained_nonzero_audit_exits=nonzero,same_optimized_proof_binary_sha256=binary,fixtures=fx['results'],scanner='NKC_SCAN.json',walker=dict(canonical='evidence/axaudit2-20261102/NEP_WALKER.lean',source='NKC_WALKER_SOURCE.lean.txt',byte_identical=True,sha256=H(canonical),object_pins=actual,driver_diffs=['NKC_Driver.diff','NKC_ProofDriver.diff'],native_link_inputs_byte_identical_to_NJW=True),resources=resources,security_target_established=False,cold_release_replay=False))
put('NKC_RESOURCES.json',resources)
assert J(E/'NKC_PREDECESSOR_COMPARISON.json')['status']=='PASS'
assert J(E/'NKC_NATIVE_REVIEW.json')['status']=='PASS_READ_ONLY_REVALIDATION'
assert J(E/'NKC_NJY_COVERAGE.json')['status']=='PASS_READ_ONLY_SEGMENT_FRAME_AND_RECORD_REVIEW'

assert J(E/'NKC_OWNER_COMPARISON.json')['status']=='PASS'
review=J(E/'NKC_CANDIDATE_REVIEW.json');assert len(review['rows'])==30 and review['no_double_count']
assert J(E/'NKC_L039/receipt.json')['exit_status']==0
basis=J(P/'NJW_LEDGER.json.xz');ledger=copy.deepcopy(basis);oldby={r['row']:r for r in basis['rows']};by={r['row']:r for r in ledger['rows']};changes=[]
for c in review['rows']:
 r=by[c['row']];assert r['status']=='OPEN'and r['obligation_statement_hash']==c['basis_obligation_statement_hash']
 o=copy.deepcopy(r['obligation']);o['basis_obligation']=copy.deepcopy(r['obligation']);o['certificate']=c['certificate'];o['kernel_roots']=c['kernel_statements'];o['NKC_complete_clause_review']=c['original_clauses'];o['NKC_hypothesis_inventory']=c['hypothesis_inventory'];o['NKC_root_domain']=c['root_domain'];o['NKC_semantic_review']=c['review']
 primary=next(k for k in c['kernel_statements']if k['root']==c['primary_root'])
 r.update(previous_status='OPEN',status='CLOSED',obligation=o,owner_module=primary['owner_module'],owner_role='canonical checked row packet',root_owners=[dict(root=x['root'],owner_module=x['owner_module'],obligation_statement_sha256=H(x['obligation_statement'].encode()))for x in c['kernel_statements']],evidence_dir='evidence/ledger17-20261108')
 changes.append(dict(row=r['row'],provider=c['provider'],previous_status='OPEN',status='CLOSED',primary_root=c['primary_root'],owner_module=r['owner_module'],basis_obligation_statement_hash=c['basis_obligation_statement_hash'],domain=c['root_domain'],roots=r['root_owners'],caller_clauses='All original clauses retained verbatim; NKC_PARENT_CLAUSES.json records the exact own-domain and unit-context requirements at every actual parent.'))
parent=J(E/'NKC_PARENT_CLAUSES.json')
for rid in parent['parents']:
 r=by[rid];o=r['obligation'];o['NKC_parent_basis_obligation']=copy.deepcopy(oldby[rid]['obligation']);o['NKC_explicit_child_domains']=[c for c in parent['clauses']if c['parent']==rid]
 o['caller_domain_obligations'] += [c['caller_clause']for c in parent['clauses']if c['parent']==rid]
for c in changes:
 r=by[c['row']];r['obligation_statement_hash']=H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode());c['complete_obligation_statement_hash']=r['obligation_statement_hash']
for rid in parent['parents']:
 r=by[rid];r['obligation_statement_hash']=H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode())
# Retain the existing (aw) supplement exactly;115 stays closed as stated.
supplement=copy.deepcopy(basis['supplemental_child_obligations'][0])
assert supplement['status']=='OPEN'
ledger['supplemental_child_obligations']=copy.deepcopy(basis['supplemental_child_obligations'])
# Never delete the spurious-by-name inventory edge.
r=by['TX1:069'];assert by['TX1:202']['function']in r['canonical_callees']
edge=dict(caller='TX1:069',callee='TX1:202',status='RECLASSIFIED_SPURIOUS_BY_NAME',ruling='(az)(1)',reason='Frozen body calls derived QueryScan::default, not IncrementalMerkleTreeV1::default',edge_retained=True)
ledger['inventory_edge_reclassifications']=basis.get('inventory_edge_reclassifications',[])+[edge]
r['obligation']['NKC_spurious_by_name_edges']=[edge]
r['obligation_statement_hash']=H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode())
rt=J(E.parent/'tx2-decoders3-20261108/NJY_REVIEWED_TRANSCRIPTIONS.json')['items']
ledger['reviewed_transcription_inventory']=basis.get('reviewed_transcription_inventory',[])+rt
put('NKC_TRUST_INVENTORY.json',dict(runtime_cryptographic_rows_unchanged=True,added_reviewed_transcription_items=rt,removed=[],classification='P6/D188 option-A RECLASSIFICATION, never removal',runtime_rows_sha256=H(json.dumps(basis['trust_rows'],sort_keys=True).encode()),boundary='NJY-B1 wrapper consumers48/49 OPEN; digest/error43/44 retained'))
counts=dict(collections.Counter(r['status']for r in ledger['rows']));assert counts=={'CLOSED':514,'OPEN':85};assert ledger['trust_rows']==basis['trust_rows']
ledger.update(basis='NJW ledger16 plus30 NKC-gated NJS/NJT/NJV/NJY occurrences; original clauses retained',basis_delta='NKC_LEDGER_DELTA.json',counts=counts,gate='PASS',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),security_target_established=False)
put('NKC_LEDGER.json',ledger)
put('NKC_LEDGER_DELTA.json',dict(schema_version=1,basis='evidence/ledger16-20261108/NJW_LEDGER.json.xz',before=dict(CLOSED=484,QUALIFIED=0,OPEN=115),after=dict(CLOSED=514,QUALIFIED=0,OPEN=85),new_closed_rows=[c['row']for c in changes],new_count=30,rows=changes,no_double_count=True,no_other_status_change=True,gate=[r['attempt']for r in rs],explicit_parent_clause_updates=parent,new_child_obligations=[],retained_child_obligations=[supplement],inventory_edge_reclassifications=[edge],reviewed_transcription_additions=rt,trust_rows_changed=False,security_target_established=False,supporting_imports_without_credit=['NJQ','NJP support already credited by NJW','all other inherited supporting modules'],rejected_candidates=[]))
review['status']='PASS_COMPLETE_STATEMENTS_EMISSION_OWNERS_AND_FULL_GATE';review['gate_pass']=True
for c in review['rows']:
 c.pop('admissible_pending_gate',None);c['gate_admitted']=True
put('NKC_CANDIDATE_REVIEW.json',review)
from NKC_report import report
report(ledger,resources)
print(json.dumps(dict(status='PASS',closed=514,open=85,qualified=0,roots=len(required),modules=len(scan),scopes=len(rs))))
