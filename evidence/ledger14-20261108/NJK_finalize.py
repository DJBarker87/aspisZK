from pathlib import Path
import json,lzma,hashlib,collections,subprocess,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def put(n,x):
 raw=(json.dumps(x,indent=1,sort_keys=True)+'\n').encode();p=E/n
 if len(raw)>20_000_000 or n=='NJK_LEDGER.json':
  Path(str(p)+'.xz').write_bytes(lzma.compress(raw,preset=6));Path(str(p)+'.sha256').write_text(H(raw)+'\n');p.unlink(missing_ok=True)
 else:p.write_bytes(raw)
required=J(E/'NJK_AUDIT_ROOTS.json')['roots'];results=[];disagreements=[];nonzero=[]
for i in range(30):
 d=J(E/f'NJK_audit/batch{i}/proof{i}.json');results+=d['results']
 if d['exit_status']:nonzero.append(f'NJK_L{i+9:03}')
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},r['root']
  if not r['equal']:disagreements.append(dict(batch=i,**r))
assert len(results)==len(required)==len({r['root']for r in results})and{r['root']for r in results}==set(required)
assert[r['root']for r in disagreements]==['NHC_DecodeModel.decoder_error']
fx=J(E/'NJK_audit/fixtures/fixtures.json');oldfx=J(E.parent/'ledger13-20261107/NIU_audit/fixtures/fixtures.json');assert fx['exit_status']==0 and fx['results']==oldfx['results']and len(fx['results'])==8
scan=[json.loads(l)for l in(E/'NJK_LOADED_scan.jsonl').read_text().splitlines()];assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
assert J(E/'NJK_audit/scan/scan.json')['exit_status']==0
put('NJK_SCAN.json',dict(exit_status=0,modules=len(scan),declarations=sum(r['declarations']for r in scan),references=sum(r['edges']for r in scan),dangling=0,incompatible_owners=0,import_mismatches=0,compatible_cached_replicas=sum(len(r['cached_replicas'])for r in scan),scanner='NFX method; NIU_Driver module/root/path-only adaptation',attempt='NJK_L008',full_combined_import='NJK_COMBINED_IMPORT',canonical_duplicate_owners=0))
rs=[json.loads(l)for l in(E/'NJK_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rs)==40 and len({r['attempt']for r in rs})==40
assert rs[-1]['attempt']=='NJK_L040'and rs[-1]['exit_status']==0
for r in rs:
 a=r['attempt'];ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 rc=J(E/a/'receipt.json');assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(rc['swaps'])=='0'and rc['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-ledger14-20261108/NJK_target'
 assert r['exit_status']==0 or a in nonzero
resources=dict(scopes=len(rs),kinds=dict(collections.Counter(r['kind']for r in rs)),wall_seconds=sum(r['wall_seconds']for r in rs),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rs),swaps=sum(int(r['swaps'])for r in rs),retained_tool_nonzero_exits=[dict(attempt=r['attempt'],target=r['module'],exit=r['exit_status'])for r in rs if r['exit_status']],kani=0,extraction=0,aggregation16G_scopes=0)
binary=J(E/'NJK_L006/NJK_ProofDriver_BINARY_PIN.json')['sha256']
for r in rs:
 p=E/r['attempt']/'NJK_ProofDriver_BINARY_PIN.json'
 if p.exists():assert J(p)['sha256']==binary
oldAudit=J(E.parent/'ledger13-20261107/NIU_AUDIT.json');canonical=subprocess.check_output(['git','show','HEAD:evidence/axaudit2-20261102/NEP_WALKER.lean'],cwd=R);assert H(canonical)==oldAudit['walker']['sha256'];(E/'NJK_WALKER_SOURCE.lean.txt').write_bytes(canonical)
sel=J(E/'NJK_L004/receipt.json')['deps_fingerprint']['selected_objects'];actual=[v for k,v in sel.items()if k.endswith('/NFA_WALKER.olean')];assert len(actual)==1 and actual[0]['sha256']==oldAudit['walker']['object_pins'][0]['sha256']
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:assert(E/'NJK_L006/sources/NJK_native'/n).read_bytes()==(E.parent/'ledger13-20261107/NIU_L007/sources/NIU_native'/n).read_bytes()
put('NJK_AUDIT.json',dict(status='PASS_REQUIRED_RAW_ROOTS_WITH_RETAINED_TOOL_FINDING',full_composition_pass=True,combined='NJK_COMBINED_IMPORT',combined_attempt='NJK_L001',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(required),all_required_raw_roots_present=True,raw_standard_axioms_only=True,axioms=sorted({a for r in results for a in r['walked_axioms']}),collect_axioms_disagreements=disagreements,raw_authoritative_ruling="(ab')(3)",retained_nonzero_audit_exits=nonzero,same_optimized_proof_binary_sha256=binary,fixtures=fx['results'],scanner='NJK_SCAN.json',walker=dict(canonical='evidence/axaudit2-20261102/NEP_WALKER.lean',source='NJK_WALKER_SOURCE.lean.txt',byte_identical=True,sha256=H(canonical),object_pins=actual,driver_diffs=['NJK_Driver.diff','NJK_ProofDriver.diff'],native_link_inputs_byte_identical_to_NIU=True),resources=resources,security_target_established=False,cold_release_replay=False))
put('NJK_RESOURCES.json',resources)
assert J(E/'NJK_PREDECESSOR_COMPARISON.json')['status']=='PASS'
prov=J(E/'NJK_OBSERVER_PROVENANCE.json');closure=J(E/'NJK_CLOSURE_PINS.json.xz');obs=next(x for x in closure['selected_objects']if x['module']=='AdapterRwModel'and x['path'].endswith('.olean'));assert obs['sha256']==prov['selected_object']['sha256'];lp=E/'NJK_L039/stdout.log';log=lp.read_text()if lp.exists()else lzma.decompress(Path(str(lp)+'.xz').read_bytes()).decode();assert'NJK_OBSERVER_OWNER AdapterRwModel'in log and 'ok' in log and 'none' in log
assert J(E/'NJK_L039/receipt.json')['exit_status']==0 and all('sorryAx'not in x for x in J(E/'NJK_L039/receipt.json')['print_axioms'])
prov.update(status='PASS_CANONICAL_PINNED_EMISSION_AND_FROZEN_OBSERVER_BODY',kernel_inspection='NJK_L039',selected_object_pin='NJK_L040',same_canonical_object=True);put('NJK_OBSERVER_PROVENANCE.json',prov)
for pre in ['NJF','NIX','NJH']:assert J(E/f'NJK_{pre}_REVALIDATION.json')['status']=='PASS'
review=J(E/'NJK_CANDIDATE_REVIEW.json');assert len(review['rows'])==7 and review['no_double_count']
b=J(E.parent/'ledger13-20261107/NIU_LEDGER.json.xz');oldby={r['row']:r for r in b['rows']};by=__import__('copy').deepcopy(oldby);changes=[]
for c in review['rows']:
 r=by[c['row']];assert r['status']=='OPEN'and r['obligation_statement_hash']==c['basis_obligation_statement_hash']
 if not c['admissible']:assert c['row']=='TX1:142';continue
 o=dict(r['obligation']);o['basis_obligation']=r['obligation'];o['certificate']=c['certificate'];o['kernel_roots']=c['complete_kernel_statements'];o['NJK_complete_clause_review']=c['basis_clauses'];o['NJK_semantic_review']=c['semantic_review'];o['NJK_hypothesis_inventory']='NJK_HYPOTHESIS_INVENTORY.json'
 r['obligation']=o;r['previous_status']='OPEN';r['status']='CLOSED';r['evidence_dir']='evidence/'+{'NJF':'slice-d-pair8-20261107','NIX':'verify-observed5-20261107','NJH':'entry-leaves-20261107'}[c['provider']]
 ordered=sorted(c['roots'],key=lambda x:x['root']!=c['primary_root']);r['root_owners']=[dict(root=x['root'],owner_module=x['owner_module'],obligation_statement_sha256=x['statement_sha256'])for x in ordered]
 r['owner_module']=r['root_owners'][0]['owner_module'];r['owner_role']='canonical primary root of complete hybrid packet, original domain retained';r['obligation_statement_hash']=H(json.dumps(o,sort_keys=True,separators=(',',':')).encode())
 changes.append(dict(row=r['row'],provider=c['provider'],previous_status='OPEN',status='CLOSED',owner_module=r['owner_module'],primary_root=c['primary_root'],roots=r['root_owners'],basis_obligation_statement_hash=c['basis_obligation_statement_hash'],complete_obligation_statement_hash=r['obligation_statement_hash'],domain=c['root_domain'],caller_clause=c['semantic_review']['caller']))
counts=dict(collections.Counter(r['status']for r in by.values()));assert counts=={'CLOSED':438,'OPEN':161}and len(changes)==6
for rid,r in by.items():
 if rid not in[r['row']for r in changes]:assert r==oldby[rid]
for rid in ['TX1:142','TX1:137','TX1:136','TX1:094','TX2:065','TX2:064','TX1:330','TX2:213']:assert by[rid]['status']=='OPEN'
assert by['TX2:115']['status']==by['TX2:129']['status']=='CLOSED'
ledger=dict(b,basis='NIU ledger13 plus six NJK-gated NJF/NIX/NJH occurrences; TX1:142 rejected',basis_delta='NJK_LEDGER_DELTA.json',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),gate='PASS',counts=counts,rows=list(by.values()),security_target_established=False);assert ledger['trust_rows']==b['trust_rows']
put('NJK_LEDGER.json',ledger)
put('NJK_LEDGER_DELTA.json',dict(schema_version=1,basis='evidence/ledger13-20261107/NIU_LEDGER.json.xz',before=dict(CLOSED=432,QUALIFIED=0,OPEN=167),after=dict(CLOSED=438,QUALIFIED=0,OPEN=161),new_closed_rows=[x['row']for x in changes],new_count=6,rows=changes,rejected_candidates=[dict(row='TX1:142',status='OPEN',module='NIX_ValidatedCut / NIX_DispatchRun',reason=next(c['semantic_review']for c in review['rows']if c['row']=='TX1:142'))],supporting_imports_without_credit=['NIW','NIY','NIZ','NIV','NJA','NJD','NJC'],gate=[f'NJK_L{i:03}'for i in range(1,41)],no_other_status_change=True,no_double_count=True,TX1_215_count=1,trust_rows_changed=False,security_target_established=False))
check=J(E/'NJK_OWNER_CHECK.json');check.update(status='PASS',selected_closure_pin='NJK_L040');put('NJK_OWNER_CHECK.json',check)
review.update(status='SIX_ADMITTED_FULL_GATE_PASS_ONE_REJECTED');put('NJK_CANDIDATE_REVIEW.json',review)
from NJK_report import report
report(ledger,resources)
print(json.dumps(dict(stage='finalize',status='PASS',CLOSED=438,OPEN=161,roots=len(required),modules=len(scan),scopes=40)))
