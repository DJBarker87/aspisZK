"""Admit only after the full combined raw/coherence gate; preserve original obligations."""
from pathlib import Path
import json,lzma,hashlib,collections,subprocess,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];H=lambda raw:hashlib.sha256(raw).hexdigest()
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def put(n,x):
 raw=(json.dumps(x,indent=1,sort_keys=True)+'\n').encode();p=E/n
 if len(raw)>20_000_000 or n=='NIU_LEDGER.json':
  Path(str(p)+'.xz').write_bytes(lzma.compress(raw,preset=6));Path(str(p)+'.sha256').write_text(H(raw)+'\n');p.unlink(missing_ok=True)
 else:p.write_bytes(raw)
required=J(E/'NIU_AUDIT_ROOTS.json')['roots'];results=[];disagreements=[];nonzero=[]
for i in range(30):
 d=J(E/f'NIU_audit/batch{i}/proof{i}.json');results+=d['results']
 if d['exit_status']:nonzero.append(f'NIU_L{i+10:03}')
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},r['root']
  if not r['equal']:disagreements.append(dict(batch=i,**r))
assert len(results)==len(required)==len({r['root']for r in results}) and {r['root']for r in results}==set(required)
assert [r['root']for r in disagreements]==['NHC_DecodeModel.decoder_error']
fx=J(E/'NIU_audit/fixtures/fixtures.json');oldfx=J(E.parent/'ledger12-20261107/NIR_audit/fixtures/fixtures.json');assert fx['exit_status']==0 and fx['results']==oldfx['results']
scan=[json.loads(l)for l in(E/'NIU_LOADED_scan.jsonl').read_text().splitlines()];assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
put('NIU_SCAN.json',dict(exit_status=J(E/'NIU_audit/scan/scan.json')['exit_status'],modules=len(scan),declarations=sum(r['declarations']for r in scan),references=sum(r['edges']for r in scan),dangling=0,incompatible_owners=0,import_mismatches=0,compatible_cached_replicas=sum(len(r['cached_replicas'])for r in scan),scanner='NFX method; NIR_Driver module/root/path-only adaptation',attempt='NIU_L008',full_combined_import='NIU_COMBINED_IMPORT'))
rs=[json.loads(l)for l in(E/'NIU_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rs)==40 and len({r['attempt']for r in rs})==40
assert rs[-1]['attempt']=='NIU_L040'and rs[-1]['exit_status']==0
for r in rs:
 ad=J(E/(r['attempt']+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 rc=J(E/r['attempt']/'receipt.json');assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(rc['swaps'])=='0'
 assert rc['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-ledger13-20261107/NIU_target'
resources=dict(scopes=len(rs),kinds=dict(collections.Counter(r['kind']for r in rs)),wall_seconds=sum(r['wall_seconds']for r in rs),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rs),swaps=sum(int(r['swaps'])for r in rs),failures=[dict(attempt=r['attempt'],target=r['module'],exit=r['exit_status'])for r in rs if r['exit_status']],kani=0,extraction=0,aggregation16G_scopes=0)
binary=J(E/'NIU_L007/NIU_ProofDriver_BINARY_PIN.json')['sha256']
for r in rs:
 p=E/r['attempt']/'NIU_ProofDriver_BINARY_PIN.json'
 if p.exists():assert J(p)['sha256']==binary
oldAudit=J(E.parent/'ledger12-20261107/NIR_AUDIT.json');canonical=subprocess.check_output(['git','show','HEAD:evidence/axaudit2-20261102/NEP_WALKER.lean'],cwd=R)
assert H(canonical)==oldAudit['walker']['sha256'];(E/'NIU_WALKER_SOURCE.lean.txt').write_bytes(canonical)
sel=J(E/'NIU_L005/receipt.json')['deps_fingerprint']['selected_objects'];actual=[v for k,v in sel.items()if k.endswith('/NFA_WALKER.olean')];assert len(actual)==1 and actual[0]['sha256']==oldAudit['walker']['object_pins'][0]['sha256']
for name in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 assert(E/'NIU_L007/sources/NIU_native'/name).read_bytes()==(E.parent/'ledger12-20261107/NIR_L006/sources/NIR_native'/name).read_bytes()
put('NIU_AUDIT.json',dict(status='PASS_REQUIRED_RAW_ROOTS_WITH_RETAINED_TOOL_FINDING',full_composition_pass=True,combined='NIU_COMBINED_IMPORT',combined_attempt='NIU_L001',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(required),all_required_raw_roots_present=True,raw_standard_axioms_only=True,axioms=sorted({a for r in results for a in r['walked_axioms']}),collect_axioms_disagreements=disagreements,raw_authoritative_ruling="(ab')(3)",retained_nonzero_audit_exits=nonzero,same_optimized_proof_binary_sha256=binary,fixtures=fx['results'],scanner='NIU_SCAN.json',walker=dict(canonical='evidence/axaudit2-20261102/NEP_WALKER.lean',source='NIU_WALKER_SOURCE.lean.txt',byte_identical=True,sha256=H(canonical),object_pins=actual,driver_diffs=['NIU_Driver.diff','NIU_ProofDriver.diff'],native_link_inputs_byte_identical_to_NIR=True),resources=resources,security_target_established=False,cold_release_replay=False))
put('NIU_RESOURCES.json',resources)
assert J(E/'NIU_PREDECESSOR_COMPARISON.json')['status']=='PASS'
review=J(E/'NIU_CANDIDATE_REVIEW.json');assert len(review['rows'])==25 and review['no_double_count']
assert J(E/'NIU_NIH_REVALIDATION.json')['status']=='PASS'and J(E/'NIU_NIS_REVALIDATION.json')['status']=='PASS_FINAL_AX2_NFX_ISOLATION'
b=J(E.parent/'ledger12-20261107/NIR_LEDGER.json.xz');by={r['row']:r for r in b['rows']};changes=[]
for c in review['rows']:
 r=by[c['row']];assert r['status']=='OPEN'and r['obligation_statement_hash']==c['basis_obligation_statement_hash']
 assert c['semantic_review']and c['review']=='COMPLETE_STATEMENT_REVIEW_PASS_PENDING_RAW_GATE'
 o=dict(r['obligation']);o['basis_obligation']=r['obligation'];o['certificate']=c['certificate'];o['kernel_roots']=c['complete_kernel_statements'];o['NIU_complete_clause_review']=c['basis_clauses'];o['NIU_semantic_review']=c['semantic_review']
 # No inherited clause or trust qualification is removed. The superseded certificate remains in basis_obligation.
 r['obligation']=o;r['previous_status']='OPEN';r['status']='CLOSED';r['evidence_dir']='evidence/'+('slice-d-entry6-20261107'if c['provider']=='NIS'else'verify-observed4-20261107')
 r['root_owners']=[dict(root=x['root'],owner_module=x['owner_module'],obligation_statement_sha256=x['statement_sha256'])for x in c['roots']]
 r['owner_module']=c['roots'][0]['owner_module'];r['owner_role']='kernel declaration with complete hybrid certificate and retained domain'
 r['obligation_statement_hash']=H(json.dumps(o,sort_keys=True,separators=(',',':')).encode())
 changes.append(dict(row=r['row'],provider=c['provider'],previous_status='OPEN',status='CLOSED',owner_module=r['owner_module'],roots=r['root_owners'],basis_obligation_statement_hash=c['basis_obligation_statement_hash'],complete_obligation_statement_hash=r['obligation_statement_hash'],domain=c['root_domain']))
counts=dict(collections.Counter(r['status']for r in by.values()));assert counts=={'CLOSED':432,'OPEN':167}
# Row147 is deliberately unchanged; supporting imports cannot promote parents.
assert by['TX1:147']==next(r for r in J(E.parent/'ledger12-20261107/NIR_LEDGER.json.xz')['rows']if r['row']=='TX1:147')
for rid in ['TX1:137','TX1:136','TX2:065','TX2:129','TX2:115']:assert by[rid]['status']=='OPEN'
ledger=dict(b,basis='NIR ledger12 plus gated NIS and NIH candidates',basis_delta='NIU_LEDGER_DELTA.json',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),gate='PASS',counts=counts,rows=list(by.values()),security_target_established=False)
put('NIU_LEDGER.json',ledger)
put('NIU_LEDGER_DELTA.json',dict(schema_version=1,basis='evidence/ledger12-20261107/NIR_LEDGER.json.xz',before=dict(CLOSED=407,QUALIFIED=0,OPEN=192),after=dict(CLOSED=432,QUALIFIED=0,OPEN=167),new_closed_rows=[x['row']for x in changes],new_count=25,rows=changes,evidence_replacements=[dict(row='TX1:147',new_credit=False,status='CLOSED',reason='NIH corrected import; NIR canonical row retained byte-for-data')],supporting_imports_without_credit=['NIT_COMBINED_IMPORT','NIL_COMBINED_IMPORT','NIO_COMBINED_IMPORT'],gate=['NIU_L001','NIU_L003','NIU_L008','NIU_L009']+[f'NIU_L{i+10:03}'for i in range(30)]+['NIU_L040'],no_other_status_change=True,no_double_count=True,trust_rows_changed=False,security_target_established=False))
check=J(E/'NIU_OWNER_CHECK.json');check.update(status='PASS',scan='NIU_L008',duplicate_owners=0,dangling=0);put('NIU_OWNER_CHECK.json',check)
review.update(status='ADMITTED_FULL_GATE_PASS');put('NIU_CANDIDATE_REVIEW.json',review)
domains=J(E/'NIU_CALL_DOMAIN_CHECK.json');domains['all_status_promotions_pending_full_gate']=False;put('NIU_CALL_DOMAIN_CHECK.json',domains)
from NIU_report import report
report(ledger,resources)
print(json.dumps(dict(stage='finalize',status='PASS',CLOSED=432,OPEN=167,roots=len(required),scopes=40)))
