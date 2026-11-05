from pathlib import Path
import json,lzma,hashlib,collections,subprocess,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];H=lambda b:hashlib.sha256(b).hexdigest();J=lambda p:json.loads(p.read_text());put=lambda n,x:(E/n).write_text(json.dumps(x,indent=1)+'\n')
required=J(E/'NIR_AUDIT_ROOTS.json')['roots'];results=[];disagreements=[]
for i in range(28):
 d=J(E/f'NIR_audit/batch{i}/proof{i}.json');results+=d['results']
 for r in d['results']:
  assert set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
  if not r['equal']:disagreements.append(dict(batch=i,**r))
assert len(results)==len(required)==len({r['root']for r in results}) and {r['root']for r in results}==set(required)
assert [r['root']for r in disagreements]==['NHC_DecodeModel.decoder_error']
fx=J(E/'NIR_audit/fixtures/fixtures.json');oldfx=J(E.parent/'owner-dedupe-20261107/NIM_audit/fixtures/fixtures.json');assert fx['exit_status']==0 and fx['results']==oldfx['results']
rs=[json.loads(l)for l in(E/'NIR_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rs)==40 and len({r['attempt']for r in rs})==40
binary=J(E/'NIR_L006/NIR_ProofDriver_BINARY_PIN.json')['sha256']
for r in rs:
 p=E/r['attempt']/'NIR_ProofDriver_BINARY_PIN.json'
 if p.exists():assert J(p)['sha256']==binary
 resources=dict(scopes=len(rs),kinds=dict(collections.Counter(r['kind']for r in rs)),wall_seconds=sum(r['wall_seconds']for r in rs),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rs),swaps=sum(int(r['swaps'])for r in rs),failures=[dict(attempt=r['attempt'],target=r['module'],exit=r['exit_status'])for r in rs if r['exit_status']],kani=0,extraction=0,aggregation16G_scopes=0)
walker=J(E.parent/'ledger11-20261107/NII_AUDIT.json')['walker_conformance'];expected=next(iter(walker['compiled_object_pins'].values()))['sha256']
selected=J(E/'NIR_L005/receipt.json')['deps_fingerprint']['selected_objects'];actual=[v for k,v in selected.items()if k.endswith('/NFA_WALKER.olean')];assert len(actual)==1 and actual[0]['sha256']==expected
canonical=subprocess.check_output(['git','show','HEAD:evidence/axaudit2-20261102/NEP_WALKER.lean'],cwd=R);assert H(canonical)==walker['sha256']
(E/'NIR_WALKER_SOURCE.lean.txt').write_bytes(canonical)
for name in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 own=(E/'NIR_L006/sources/NIR_native'/name).read_bytes();old=(E.parent/'owner-dedupe-20261107/NIM_L031/sources/NIM_native'/name).read_bytes();assert own==old
put('NIR_AUDIT.json',dict(status='PASS_REQUIRED_RAW_ROOTS_WITH_RETAINED_TOOL_FINDING',full_composition_pass=True,combined='NIR_COMBINED_IMPORT',combined_attempt='NIR_L002',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(required),all_required_raw_roots_present=True,raw_standard_axioms_only=True,axioms=sorted({a for r in results for a in r['walked_axioms']}),collect_axioms_disagreements=disagreements,raw_authoritative_ruling="(ab')(3)",retained_nonzero_audit_exit='NIR_L037',same_optimized_proof_binary_sha256=binary,fixtures=fx['results'],scanner='NIR_SCAN.json',walker=dict(canonical='evidence/axaudit2-20261102/NEP_WALKER.lean',source='NIR_WALKER_SOURCE.lean.txt',byte_identical=True,sha256=H(canonical),object_pins=actual,driver_diffs=['NIR_Driver.diff','NIR_ProofDriver.diff'],native_link_inputs_byte_identical_to_NIM=True),resources=resources,security_target_established=False,cold_release_replay=False))
put('NIR_RESOURCES.json',resources)
# Compare every predecessor selected module/object sidecar by logical identity, independent of copy path.
new=json.loads(lzma.decompress((E/'NIR_CLOSURE_PINS.json.xz').read_bytes()));old=json.loads(lzma.decompress((E.parent/'owner-dedupe-20261107/NIM_CLOSURE_PINS.json.xz').read_bytes()))
def key(x):
 p=x['path'];suffix=next((s for s in ['.olean.private','.olean.server','.olean','.ir']if p.endswith(s)),None);assert suffix,p
 return (x['module'],suffix)
ni={key(x):x for x in new['selected_objects']};oi={key(x):x for x in old['selected_objects']};mismatch=[dict(module=k[0],suffix=k[1],old=oi[k],new=ni.get(k))for k in oi if k not in ni or oi[k]['sha256']!=ni[k]['sha256']]
put('NIR_PREDECESSOR_COMPARISON.json',dict(previous_files=len(oi),current_files=len(ni),same_predecessor_files=len(oi)-len(mismatch),mismatches=mismatch,added_files=len(set(ni)-set(oi)),status='PASS'if not mismatch else'FINDING',meaning='Every previous selected owner object and sidecar is unchanged by SHA256; current clean scan establishes its canonical declaration ownership. Paths may differ due to seed copies.'))
assert not mismatch,mismatch[:2]
from NIR_ledger import build
rows,b,owners=build(final=True);assert collections.Counter(r['status']for r in rows)=={'CLOSED':407,'OPEN':192}
assert not J(E/'NIR_OWNER_CHECK.json')['missing_closed_roots']
put('NIR_LEDGER_DELTA.json',dict(schema_version=1,basis='NIM_LEDGER_DELTA applied to NII 599 rows',before=dict(CLOSED=407,QUALIFIED=0,OPEN=192),after=dict(CLOSED=407,QUALIFIED=0,OPEN=192),new_closed_rows=[],new_count=0,evidence_replacements=[dict(row='TX2:045',previous_status='CLOSED',status='CLOSED',previous_provider='NGC',provider='NIG',root='NIG_FilledCoverage.source',evidence_dir='evidence/slice-d-pair4-20261107',reason='Already CLOSED in NIM authoritative basis; NIG is a narrower revalidated replacement, not a second occurrence',complete_obligation_hash=next(r['obligation_statement_hash']for r in rows if r['row']=='TX2:045'))],gate=['NIR_L002','NIR_L007','NIR_L008']+[r['attempt']for r in rs if r['kind']=='audit'and r['module'].startswith('batch')],no_other_status_change=True,trust_rows_changed=False,security_target_established=False))
from NIR_report import report
report()
print('NIR full raw/coherence/ledger finalization PASS; 407 CLOSED / 192 OPEN')
