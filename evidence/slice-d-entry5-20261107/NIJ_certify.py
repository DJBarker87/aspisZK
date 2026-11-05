"""Additive one-row admission; unchanged NFK predicates plus stricter gates."""
from pathlib import Path
import json,lzma,hashlib,subprocess,re,copy,types,sys,time,resource
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];P=E.parent/'slice-d-entry4-20261106';J=E.parent/'slice-d-entry3-20261106';start=time.monotonic()
read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
def put(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
subprocess.run([sys.executable,str(E/'NIJ_entry_check.py')],check=True)
association=read(E/'NIJ_ENTRY_ASSOCIATION.json');assert association['status']=='PASS_ENTRY_NATIVE_MODEL_ASSOCIATION'
raw=read(E/'NIJ_stage1_audit/proof0.json');fx=read(E/'NIJ_stage1_audit/fixtures.json');scan=read(E/'NIJ_stage1_audit/scan_summary.json')
assert fx['exit_status']==raw['exit_status']==0 and len(fx['results'])==8 and all(x['equal'] for x in fx['results'])
assert all(len(x['walked_axioms'])==1 for x in fx['results'][:4]) and all(not x['walked_axioms'] for x in fx['results'][4:])
assert raw['same_optimized_binary_sha256']==fx['same_optimized_binary_sha256']
assert all(x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in raw['results'])
assert scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0
basepath=E.parent/'ledger10-20261106/NHO_LEDGER.json.xz';data=lzma.decompress(basepath.read_bytes());base=json.loads(data);by={r['row']:r for r in base['rows']};assert len(by)==599
v=(E/'NIJ_NFK_validate.py.txt').read_bytes();original=subprocess.check_output(['git','show','HEAD:evidence/slice-d-entry-20261105/NGL_NFK_validate.py.txt'],cwd=R);assert v==original
n=types.ModuleType('NIJ_retained_NFK');n.__file__=str(E/'NIJ_NFK_validate.py.txt');exec(compile(v,n.__file__,'exec'),n.__dict__);n.BASE_CREDITS=base['NEZ_credits']
# Prior CLOSED rows are used by immutable certificate, never replayed or double-counted.
inherited={};certs={};candidates={};provenance=[]
for root,prefix in [(J,'NHJ'),(P,'NHY')]:
 delta=read(root/(prefix+'_LEDGER_DELTA.json'));closed=read(root/(prefix+'_CLOSED.json'));cc={c['id']:c for c in closed['functions']}
 for row in delta['rows']:
  rid=row['row'];assert rid not in inherited
  inherited[rid]=copy.deepcopy(row);candidates[rid]=(prefix,copy.deepcopy(row));certs[rid]=cc[row['selected_claims'][0]]
 for f in [root/(prefix+'_LEDGER_DELTA.json'),root/(prefix+'_CLOSED.json'),root/(prefix+'_AUDIT.json')]:provenance.append(dict(path=str(f.relative_to(R)),sha256=sha(f.read_bytes()),bytes=f.stat().st_size))
assert len(inherited)==28
rid='TX2:202';template=next(c for c in read(P/'NHY_CLOSED.json')['functions'] if c['id']=='NHY::decode_registry_v2')
c=dict(template,id='NIJ::decode_entry_v2',subject=by[rid]['function'],route='y/ai/ak: actual original-buffer/status/constructor packet + full Result SSA + CLOSED validator',model_theorem='NIJ_EntryJoin.cohort',root_domain='Every valid immutable Rust byte slice, every length and byte content. Non320 rejects before payload. Length320 proves all exact field/status/read/unwrap domains. No successful header or validator premise.',inner_hypotheses_remaining=[],native_passes=['NHY_K051','NHY_K055','NHY_K059','NHY_K095','NHY_K108','NIJ_K056'],matched_controls=['NHY_K052','NHY_K056','NHY_K060','NHY_K096','NHY_K109','NIJ_K057'],callee_laws={'status':'TX2:192 CLOSED NHY::status every u8. Actual bytes[5] call and rejection before further constructor reads are included in exact native producer NIJ_K056/057, model NIJ_EntryStatus.rejected.', 'validator':'TX2:207 CLOSED NHY::entry_v2_validator every full typed record. Producer NIJ_K056/057 observes all scalars plus every byte via arbitrary field/j; NHY_RecordExt.entry_injective and two-sided NCX_Carrier ports identify SAME full argument. No validation success condition.', 'reads/casts':'All original320-byte read ranges and4 byte offsets enumerated and bounds proved; original-window K051/052,K055/056; exact NCX cast/word packets and KMX laws by retained hash. Producer K056 executes all actual source reads and compares words/bytes independently.', 'return':'NHY_K108/109 transports every error and exact success record from independent SAME post-read SSA fields. Actual frozen suffix is exactly validate(&entry)?;Ok(entry).'},source_association='NIJ_ENTRY_ASSOCIATION.json and NIJ_entry_check.py check original frozen constructor/status ?, full source header/suffix, native exact source snapshots, all scalar/window domains and controls. NIJ_EntryModel.source universal first-error natural body, NIJ_EntryJoin selects actual NCX_Install.op34 with complete NCX ports; slots43/44 preserved.',effects='Pure shared immutable original byte buffer/record; no allocation, account write, mutable static or discarded cleanup. Complete Result errors preserved. Exact lengths establish reached unwrap domains.',combined='NIJ_L018',audit=['NIJ_L021 raw20 roots and eight controls, NFX scan exit0'],trust_reclassification='Retained P6/D188 option-A native semantic transport and std/compiler/ABI realization, reclassified not removed. No new runtime trust.',root_model='AspisR1.RPx_Deployed.deployed; frozen3; L154 parameter')
c.pop('semantic_review_sha256',None);c['semantic_review_sha256']=sha(json.dumps(c,sort_keys=True).encode())
r=copy.deepcopy(by[rid]);assert r['composed_status']=='OPEN' and not r['named_hypotheses'];r.update(composed_status='CLOSED',bridge_status='CLOSED-CONDITIONAL',selected_claims=[c['id']],active_support_receipts=[str((E/a/'receipt.json').relative_to(R)) for a in ['NIJ_K056','NIJ_K057']],open_transitive_dependencies=[],composed_reason='Universal current-entry decoder: exact original constructor/status native packet, header/windows/full Result return packets by SHA, CLOSED full-domain validator, full natural emitted/cohort equality, coherent ax2/NFX. No success/output equality premise.')
reasons={'len':'Every usize descriptor, wrong length before reads; exact std metadata and retained K008/009.', 'Err':'Exact source first-error label; complete error port and native/status/header rejection.', 'Ok':'Same complete post-read SSA record after validator, NHY_K108/109 and NHY_RecordExt.entry_injective.', 'unwrap':'Every reached cast receives exact32/8 bytes from original320 source. All bounds explicit in NIJ_EntryModel/Record.', 'try_into':'Original field windows native K051/052,K055/056 plus new full original constructor NIJ_K056/057 and exact retained KMX/NCX cast laws.', 'from_le_bytes':'Exact original264/272 eight-byte words, independent scalar-shift reference NIJ_K056/057 and NHY_NaturalReads.word.'}
for o in r['caller_domain_obligations']:
 if 'callee' in o:
  if o['callee'].endswith('::try_from'):claim='NHY::status';why=c['callee_laws']['status']
  else:assert o['callee'].endswith('::validate_verifier_registry_entry_v2');claim='NHY::entry_v2_validator';why=c['callee_laws']['validator']
  o.update(status='CLOSED',callee_claims=[claim],discharged_by='NIJ::decode_entry_v2: '+why)
 else:
  name=o['call']['name'];assert name in reasons,name;o.update(status='CLOSED',discharged_by='NIJ::decode_entry_v2: '+reasons[name])
assert not n.row_checks(r,by[rid],c),n.row_checks(r,by[rid],c)
n.certificate_checks(type('Support',(),{'support':lambda self,c:None})(),c)
candidates[rid]=('NIJ',r);certs[rid]=c
tiny=copy.deepcopy(base);tiny['rows']=[copy.deepcopy(by[x]) for x in candidates]
admitted=n.admit(tiny,candidates,certs,{'NIJ':[rid],'NHJ':[x for x in inherited if candidates[x][0]=='NHJ'],'NHY':[x for x in inherited if candidates[x][0]=='NHY']})
newby=dict(by);newby.update({x['row']:x for x in admitted['rows']});assert newby[rid]['composed_status']=='CLOSED' and all(newby[x]['composed_status']=='CLOSED' for x in inherited)
assert all(newby[x]['composed_status']==by[x]['composed_status'] for x in by if x not in candidates)
# Denial controls: inherited selected children are real dependencies, never cosmetic edges.
mutations=[]
bad=copy.deepcopy(r);bad['frozen_body_sha256']='0'*64;assert 'candidate frozen identity mismatch' in n.row_checks(bad,by[rid],c);mutations.append('frozen source identity')
bad=copy.deepcopy(r);bad['caller_domain_obligations'][0]['status']='OPEN';assert 'Open caller-domain obligation' in n.row_checks(bad,by[rid],c);mutations.append('caller domain')
try:n.certificate_checks(type('Support',(),{'support':lambda self,c:None})(),dict(inner_hypotheses_remaining=['unpaired stub']))
except ValueError:mutations.append('residual inner hypothesis')
else:raise AssertionError('residual accepted')
for child in ['TX2:192','TX2:207']:
 mutated=copy.deepcopy(candidates);rr=mutated[child][1];rr['composed_status']='OPEN';rr['bridge_status']='OPEN';mutated[child]=(mutated[child][0],rr)
 denied=n.admit(tiny,mutated,certs,{'NIJ':[rid]});assert next(x for x in denied['rows'] if x['row']==rid)['composed_status']=='OPEN';mutations.append('selected child denial '+child)
assert lzma.decompress(basepath.read_bytes())==data
put('NIJ_CLOSED.json',dict(schema_version=1,frozen_revision=base['frozen_revision'],new_composed_functions=1,new_composed_rows=1,functions=[c],driver_root_status='OPEN'))
put('NIJ_EDGES.json',dict(edges=r['caller_domain_obligations'],no_out_of_slice_credit=True))
counts={status:sum(x['composed_status']==status for x in newby.values()) for status in ['CLOSED','OPEN','QUALIFIED']}
put('NIJ_LEDGER_DELTA.json',dict(baseline=str(basepath.relative_to(R)),baseline_uncompressed_sha256=sha(data),new_closed_rows=[rid],rows=[r],inherited_rows=list(inherited),inherited_provenance=provenance,no_other_status_change=True,validator_checks_added_only=True,unchanged_NFK_validator_sha256=sha(v),checks_added=['exact complete original-buffer constructor including status and all fields','frozen graph/offline/lock/features/KMX matched semantic negative','universal source/model, same record and full Result association','NGK/RPx coherent import, ax2 same optimized binary/eight fixtures, standard axioms; NFX zero defects','unchanged NFK predicates, selected status/validator denial propagation'],whole_ledger_counts_after_inherited_and_new=counts,baseline_preserved_byte_exactly=True,mutation_denials=mutations,trust_reclassification='P6/D188 option-A retained; nothing removed'))
put('NIJ_AUDIT.json',dict(status='PASS_AX2_NFX',combined='NIJ_L018',roots=raw['results'],fixtures=fx,scan=scan,walker_sha256=read(E/'NIJ_WALKER_PIN.json')['sha256'],driver_diffs=['NIJ_ProofDriver.diff','NIJ_ScanDriver.diff'],scope='Focused coherent cached replay; no cold release-manifest or ELF reproduction claim',standard_axioms_only=True))
put('NIJ_LOCAL_VALIDATION.json',dict(target='NIJ_entry_check + unchanged NFK row/certificate/admit with five denial controls',exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//(1024 if sys.platform=='darwin' else 1),swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_sha256=sha(Path(__file__).read_bytes()),print_axioms='N/A Python; exact formal roots in NIJ_AUDIT.json',new_closed_rows=1))
print(json.dumps(dict(status='PASS',new_closed_rows=1,counts=counts,denials=mutations)))
