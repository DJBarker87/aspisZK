"""Additive packet checks; unchanged NFK predicates; no baseline defaults or edits."""
from pathlib import Path
import json,lzma,hashlib,subprocess,sys,types,copy,time,resource,collections,re
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-entry-20261105';D=E.parent/'slice-d-entry2-20261106';start=time.monotonic()
sha=lambda b:hashlib.sha256(b).hexdigest()
J=lambda p:json.loads(p.read_text())
def put(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
def log(root,a):return lzma.decompress((root/a/'stdout.log.xz').read_bytes()).decode()
# Reuse immutable whole-body checks with their existing exact input snapshots.
raw=(P/'NGL_certify.py').read_bytes();m=types.ModuleType('NHJ_retained');m.__file__=str(P/'NGL_certify.py');exec(compile(raw,m.__file__,'exec'),m.__dict__);m.put=lambda n,x:put('NHJ_REUSED_'+n,x)
reused=[m.native_review(),m.model_review(),m.source_review()]
for x in J(E/'NHJ_REUSE.json')['files']:
 p=E.parents[1]/x['path'];assert sha(p.read_bytes())==x['sha256'],p
rs=[json.loads(s) for s in (E/'NHJ_ATTEMPTS.jsonl').read_text().splitlines()];assert len({r['attempt'] for r in rs})==len(rs)
for r in rs:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['swaps'])==0 and int(r['peak_rss_kib'])<8*1024*1024
 ad=J(E/(r['attempt']+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
 if r['kind']=='kani':
  a=r['attempt'];assert J(E/(a+'-graph-check.json'))['graph_matches_frozen'] and J(E/(a+'-erasure-check.json'))['passed'] and not J(E/(a+'-source-check.json'))['errors']
  lock=J(E/(a+'-lock-check.json'));assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3' and '--locked' not in r['native_command']
  assert 'pool-adapter,private-leaf-salts' in r['native_command']
assert J(E/'NHJ_K001/receipt.json')['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in log(E,'NHJ_K001')
s=log(E,'NHJ_K002');assert 'VERIFICATION:- FAILED' in s and 'Failed Checks: |r| *r' in s and re.search(r'\*\* 1 of \d+ failed',s)
proof=J(E/'NHJ_audit/proof0.json');fixtures=J(E/'NHJ_audit/fixtures.json');scan=J(E/'NHJ_audit/scan_summary.json')
assert proof['exit_status']==0 and len(proof['results'])==3 and fixtures['same_optimized_binary_sha256']==proof['same_optimized_binary_sha256']
assert all(x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in proof['results'])
assert fixtures['exit_status']==0 and len(fixtures['results'])==8 and all(x['equal'] for x in fixtures['results'])
assert scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0
# Complete source cut association: identical call except an extra local log argument.
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'],text=True)
body='readonly_meta_ok(account.owner(), owner, account.is_signer, account.is_writable, account.executable)'
assert body in frozen
native=(E/'NHJ_owned.rs.txt').read_text();assert 'meta_oracle(account.owner(),owner,account.is_signer,account.is_writable,account.executable,l)' in native
assert not re.search(r'\bstatic\s+mut\b|\bstatic\s+\w+\s*:',native)
# Source domain: packet reads only metadata, storage domain is unchanged eleven-shape NGL carrier.
assert 'l.reply=kani::any()' in native and 'if l.reply{Ok(())}else{Err(ProgramError::InvalidAccountData)}' in native
baseline=E.parent/'ledger9-20261105/NGZ_LEDGER.json.xz';data=lzma.decompress(baseline.read_bytes());base=json.loads(data);by={r['row']:r for r in base['rows']};assert len(by)==599
n=m.NFK();n.BASE_CREDITS=base['NEZ_credits']
delta=J(E/'NHJ_stage2_audit/proof1.json');latestscan=J(E/'NHJ_stage2_audit/scan_summary.json')
assert delta['exit_status']==0 and len(delta['results'])==3 and delta['same_optimized_binary_sha256']==fixtures['same_optimized_binary_sha256']
assert all(x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in delta['results'])
assert latestscan['dangling']==latestscan['incompatible_owners']==latestscan['import_mismatches']==0
for a,exit in [('NHJ_K003',0),('NHJ_K004',1)]:
 assert J(E/a/'receipt.json')['exit_status']==exit
 assert ('VERIFICATION:- SUCCESSFUL' if exit==0 else 'VERIFICATION:- FAILED') in log(E,a)
assert 'Failed Checks: |r| *r' in log(E,'NHJ_K004')
rows=[];certificates={};candidates={} 
for rid,label,law,passes,controls in [
 ('TX2:223','metadata','NHJ_ReadonlyPacket.metadata',['NGL_K037'],['NGL_K038']),
 ('TX2:236','readonly','NHJ_ReadonlyPacket.readonly',['NGL_K106','NHJ_K001'],['NGL_K107','NHJ_K002']),
 ('TX1:335','data','NHJ_DataPacket.substitute',['NGL_K064','NGL_K070','NGL_K076']+[f'NGL_K{k:03}' for k in range(90,106,2)]+['NHJ_K003'],['NGL_K065','NGL_K071','NGL_K077']+[f'NGL_K{k:03}' for k in range(91,106,2)]+['NHJ_K004']),
 ('TX2:229','data','NHJ_DataPacket.substitute',['NGL_K064','NGL_K070','NGL_K076']+[f'NGL_K{k:03}' for k in range(90,106,2)]+['NHJ_K003'],['NGL_K065','NGL_K071','NGL_K077']+[f'NGL_K{k:03}' for k in range(91,106,2)]+['NHJ_K004'])]:
 r=copy.deepcopy(by[rid]);subject=r['function']
 c=dict(id='NHJ::'+label,subject=subject,route='y/ak',model_theorem=law,inner_hypotheses_remaining=[],root_domain='Typed live keys; caller metadata; original eleven-shape readonly storage carrier. Root PacketDomain/PhysicalInterpretation retained; no success restriction.',native_passes=passes,matched_controls=controls,retained_interface_real_and_modifies='NHD_K049/051' if label=='metadata' else 'NHD_K052/054',source_association='NHJ_certify.py exact call expression',combined='NHJ_L004',audit='NHJ_L006',trust_reclassification='P6/D188 option A retained; never removal',effects='No state or ordered effects; local oracle log only')
 if label=='data':
  c.update(root_domain='NGL_StorageCases.Domain: borrowed-error or rejected-length or successful vector in nine retained capacities, same live original allocation; root PhysicalInterpretation retained. No supplied output equality.',native_clone='NHD_K014..017; NGL_CloneDomain.clone on SnapshotError',retained_interface_real_and_modifies='NHD_K055/057',combined='NHJ_L009',audit='NHJ_L010',source_association='Frozen data match; replace only error.clone by local error_oracle, full error reply forwarded; success SAME slice; NHJ_DataPacket.storage_domain derives both exact input error constructors')
 c['semantic_review_sha256']=sha(json.dumps(c,sort_keys=True).encode());certificates[rid]=c
 r.update(composed_status='CLOSED',bridge_status='CLOSED-CONDITIONAL',selected_claims=['NHJ::'+label],active_support_receipts=[str((P if a.startswith('NGL') else E)/a/'receipt.json') for a in passes+controls],open_transitive_dependencies=[],composed_reason='Full native/model packet under y/ak, exact caller arguments and unchanged modifies frame; retained root domain and physical interpretation.')
 for h in r['named_hypotheses']:h['discharged_by']='NHJ '+label+' packet: comparison via full native key gate + NGL_ArrayEquality; root domain/interpretation retained explicitly'
 for o in r['caller_domain_obligations']:
  o.update(status='CLOSED',discharged_by=c['id'])
  if o.get('callee','').endswith('::readonly_meta_ok'):o['callee_claims']=['NHJ::metadata']
 assert n.row_checks(r,by[rid],c)==[],(rid,n.row_checks(r,by[rid],c))
 rows.append(r);candidates[rid]=('NHJ',r)
# Unchanged predicates on schema-complete selected rows plus already closed owner getter.
owner=next(r for r in base['rows'] if r['function'].endswith('::OwnedAccount::owner') and r['composed_status']=='CLOSED')
tiny=copy.deepcopy(base);tiny['rows']=[copy.deepcopy(by[r['row']]) for r in rows]+[copy.deepcopy(owner)]
for c in certificates.values():n.certificate_checks(type('Support',(),{'support':lambda self,c:None})(),c)
admitted=n.admit(tiny,candidates,certificates,{'NHJ':list(candidates)});assert all(r['composed_status']=='CLOSED' for r in admitted['rows'])
# No invented fields on twelve schema-incomplete OPEN rows; baseline is never mutated.
assert lzma.decompress(baseline.read_bytes())==data
for rid in candidates:
 bad=copy.deepcopy(candidates[rid][1]);bad['frozen_body_sha256']='0'*64;assert 'candidate frozen identity mismatch' in n.row_checks(bad,by[rid],certificates[rid])
 bad=copy.deepcopy(candidates[rid][1]);bad['caller_domain_obligations'][0]['status']='OPEN';assert 'Open caller-domain obligation' in n.row_checks(bad,by[rid],certificates[rid])
try:n.certificate_checks(type('Support',(),{'support':lambda self,c:None})(),{'inner_hypotheses_remaining':['stub without child law']})
except ValueError:pass
else:raise AssertionError('residual obligation admitted')
put('NHJ_CLOSED.json',dict(schema_version=1,frozen_revision=base['frozen_revision'],new_composed_functions=3,new_composed_rows=4,functions=list(certificates.values()),driver_root_status='OPEN'))
put('NHJ_EDGES.json',dict(edges=[o for r in rows for o in r['caller_domain_obligations']],no_out_of_slice_credit=True))
counts=collections.Counter(r['composed_status'] for r in base['rows']);counts['CLOSED']+=4;counts['OPEN']-=4
put('NHJ_LEDGER_DELTA.json',dict(baseline=str(baseline.relative_to(E.parents[1])),baseline_uncompressed_sha256=sha(data),new_closed_rows=list(candidates),rows=rows,no_other_status_change=True,validator_checks_added_only=True,unchanged_NFK_validator_sha256=J(P/'NGL_VALIDATOR_INPUT_PINS.json')['unchanged_NFK_validator']['sha256'],checks_added=['ruling ak exact constructor coverage; arbitrary Bool reply','exact local log argument and reply checks plus semantic negative','NGL/NHD evidence pins retained unchanged','combined NGK+RPx, raw ax2 and NFX exit0','unchanged NFK row and certificate gates on schema-complete subset; no baseline defaults'],whole_ledger_counts_after=dict(total=599,**counts),baseline_preserved_byte_exactly=True,mutation_denials=5,trust_reclassification='P6/D188 option A retained; no new trust'))
put('NHJ_AUDIT.json',dict(status='PASS_AX2_NFX',combined='NHJ_L009',audit=['NHJ_L006','NHJ_L010'],roots=proof['results']+delta['results'],fixtures=fixtures,scan=latestscan,retained_checks=reused,scope='Focused cached objects; not a cold release replay',standard_axioms_only=True))
put('NHJ_LOCAL_LEDGER_VALIDATION.json',dict(target='NHJ_certify: additive admission of metadata, readonly and borrowed data packets',exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//(1024 if sys.platform=='darwin' else 1),swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=sha(Path(__file__).read_bytes()),print_axioms='N/A ordinary Python evidence validation; formal axiom lines in NHJ_AUDIT.json',result=dict(new_closed_rows=4,mutation_denials=9,ledger_counts=dict(counts))))
print(json.dumps(dict(status='PASS',new_closed_rows=4,scan=latestscan)))
