"""Additive two-row snapshot admission; unchanged NFK gates and stricter receipts."""
from pathlib import Path
import json,lzma,hashlib,subprocess,re,copy,types,sys,time,resource
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];P=E.parent/'slice-d-entry-20261105';D=E.parent/'slice-d-entry2-20261106';J=E.parent/'slice-d-entry3-20261106';start=time.monotonic()
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads(p.read_text())
def put(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
def log(root,a):return lzma.decompress((root/a/'stdout.log.xz').read_bytes()).decode()
subprocess.run([sys.executable,str(E/'NHY_source_check.py')],check=True,capture_output=True)
# Keep pinned inputs once, referenced by hash, including failed source snapshots.
idx=read(E/'NHY_INPUTS.json') if (E/'NHY_INPUTS.json').exists() else dict(objects={},attempts={})
for p in sorted(E.glob('NHY_*/sources/**/*')):
 if not p.is_file():continue
 b=p.read_bytes();h=sha(b);archive=E/'NHY_INPUTS'/(h+'.xz');archive.parent.mkdir(exist_ok=True)
 if not archive.exists():archive.write_bytes(lzma.compress(b))
 idx['objects'][h]=dict(path=str(archive.relative_to(E)),bytes=len(b),archive_sha256=sha(archive.read_bytes()))
 attempt=p.relative_to(E).parts[0];rel=str(p.relative_to(E/attempt/'sources'));idx['attempts'].setdefault(attempt,{})[rel]=h
 p.unlink()
for p in sorted(E.glob('NHY_*/sources/**/*'),reverse=True):
 if p.is_dir() and not any(p.iterdir()):p.rmdir()
put('NHY_INPUTS.json',idx)
for h,x in idx['objects'].items():
 z=(E/x['path']).read_bytes();assert sha(z)==x['archive_sha256'];b=lzma.decompress(z);assert sha(b)==h and len(b)==x['bytes']
receipts=[json.loads(l) for l in (E/'NHY_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({r['attempt'] for r in receipts})==len(receipts)
for r in receipts:
 a=r['attempt'];ad=read(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['swaps'])==0 and int(r['peak_rss_kib'])<8*1024*1024
 for n,h in r['source_hashes'].items():assert idx['attempts'][a][n]==h,(a,n)
 if r['kind']=='kani':
  assert read(E/(a+'-graph-check.json'))['graph_matches_frozen']
  assert read(E/(a+'-erasure-check.json'))['passed'] and not read(E/(a+'-source-check.json'))['errors']
  lock=read(E/(a+'-lock-check.json'));assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert '--locked' not in r['native_command'] and 'pool-adapter,private-leaf-salts' in r['native_command']
for pos,neg in [('NHY_K005','NHY_K006'),('NHY_K008','NHY_K009')]:
 assert read(E/pos/'receipt.json')['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in log(E,pos)
 s=log(E,neg);assert read(E/neg/'receipt.json')['exit_status']==1 and 'timed out' not in s and re.search(r'\*\* 1 of \d+ failed',s) and re.search(r'Failed Checks: \|r\|\s*\*r',s)
for a in ['NHY_L001','NHY_L002','NHY_L009','NHY_L010']:assert read(E/a/'receipt.json')['exit_status']==0
proofs=[read(E/'NHY_stage1_audit/proof0.json'),read(E/'NHY_stage3_audit/proof1.json')];fx=read(E/'NHY_stage1_audit/fixtures.json');scan=read(E/'NHY_stage3_audit/scan_summary.json')
assert fx['exit_status']==0 and len(fx['results'])==8 and all(r['equal'] for r in fx['results'])
assert all(len(x['walked_axioms'])==1 for x in fx['results'][:4]) and all(not x['walked_axioms'] for x in fx['results'][4:])
for pr in proofs:
 assert pr['exit_status']==0 and pr['same_optimized_binary_sha256']==fx['same_optimized_binary_sha256']
 assert all(r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in pr['results'])
assert scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0
assert (P/'NGL_WALKER_SOURCE.lean.txt').read_bytes()==(E.parent/'axaudit2-20261102/NEP_WALKER.lean').read_bytes()
# Every invoked predecessor law/receipt is immutable by SHA, never rerun.
reused=[]
for root,names in [(J,['NHJ_CLOSED.json','NHJ_LEDGER_DELTA.json','NHJ_AUDIT.json','NHJ_SOURCE_ASSOCIATION.json','NHJ_QUARANTINE.json','NHJ_E001/receipt.json','NHJ_SnapshotPacket.lean','NHJ_SnapshotEntry.lean','NHJ_SnapshotAssociation.lean','NHJ_SdkBorrowPacket.lean','NHJ_StdCopy.lean','NHJ_CopyPacket.lean','NHJ_EntryDomains.lean','NHJ_SdkDomains.lean']+[f'NHJ_K{k:03}/receipt.json' for k in list(range(15,33))+[37,38,39,40,41,42,65,66,67,68,69,70,71,75,76,77,78,79,80,81]]),(D,['NHD_K014/receipt.json','NHD_K015/receipt.json','NHD_SnapshotWindows.lean']),(P,['NGL_CloneDomain.lean','NGL_SnapshotModel.lean','NGL_WALKER_SOURCE.lean.txt','NGL_NFK_validate.py.txt','NGL_VALIDATOR_INPUT_PINS.json'])]:
 for n in names:
  p=root/n;reused.append(dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes())))
put('NHY_REUSED_CERTIFICATES.json',dict(files=reused,forbidden_receipts=['NHJ_K011','NHJ_K012','NHJ_K013','NHJ_K014','NHJ_K033','NHJ_K035','NHJ_K036'],no_passing_shape_rerun=True))
basepath=E.parent/'ledger10-20261106/NHO_LEDGER.json.xz';data=lzma.decompress(basepath.read_bytes());base=json.loads(data);by={r['row']:r for r in base['rows']};assert len(by)==599
raw=(P/'NGL_NFK_validate.py.txt').read_bytes();pin=read(P/'NGL_VALIDATOR_INPUT_PINS.json')['unchanged_NFK_validator']['sha256'];assert sha(raw)==pin
n=types.ModuleType('NHY_retained_NFK');n.__file__=str(P/'NGL_NFK_validate.py.txt');exec(compile(raw,n.__file__,'exec'),n.__dict__);n.BASE_CREDITS=base['NEZ_credits']
cert=dict(id='NHY::snapshot',subject=by['TX1:343']['function'],route='y/ak staged SDK/clone/copy packets',model_theorem='NHY_SnapshotJoin.source',root_domain='Same typed AccountInfo/metadata/buffer interpretation as S2W_D189Entry.Entry.heap; relatedness and Valid of that heap are the retained root PhysicalInterpretation, no caller-success or native-output hypothesis. Actual caller firstSizes/secondSizes derive nine allocating domains1..58295; malformed-length rejection is unrestricted. Generic non-root error arm is explicitly covered by NHY_SnapshotJoin.rejected/both_arms.',inner_hypotheses_remaining=[],native_passes=['NHY_K005','NHY_K008'],matched_controls=['NHY_K006','NHY_K009'],callee_laws={'SDK':'accepted S2TrustedSdkBorrow15; NHJ bracket + NHY_SnapshotRoot.returning derives acquisition from computed zero, same payload, cleanup','clone':'NGL_CloneDomain.clone + NHY_SnapshotHeader.clone_domain/clone_reply; NHD_K014/015; sole SDK error establishes canonical domain','copy':'NHJ exact allocation/capacity, KMX byte value/frame, initialization and loop induction, set_len and nine return frames; see NHY_REUSED_CERTIFICATES.json'},source_association='NHY_SOURCE_ASSOCIATION.json, exact before-copy/header/clone source projection; unrestricted descriptor classifier, not an invented large slice; NHY_SnapshotHeader.chain is full Result chain; retained E001 extraction reused by SHA.',effects='Local logs only. Existing SDK bracket restores same heap; original metadata/buffer immutable; same fresh returned allocation and exact bytes; callee does not own input AccountInfo or returned OwnedAccount cleanup; existing abort/divergence retained.',combined='NHY_L010',audit=['NHY_L006 raw/fixtures','NHY_L007 corrected scan','NHY_L011 raw/scan'],trust_reclassification='P6/D188 option-A semantic transport, accepted SDK15/Std/compiler/allocator/ABI/source-to-ELF retained. No new trust; no RuntimeCpiReadonlyEntry7; not premise removal.',root_model='AspisR1.RPx_Deployed.deployed; frozen3; L154 parameter')
cert['semantic_review_sha256']=sha(json.dumps(cert,sort_keys=True).encode());rows=[];certs={};candidates={}
reasons={'account.try_borrow_data':'accepted SDK15, NHY_SnapshotRoot.returning and both-arm local log K005/K006; source native relation to SAME computed entry heap','data.len':'descriptor projection, unrestricted K008/K009 and NHJ_K078/079, NHJ_SnapshotEntry.len_iff','data.to_vec':'NHJ primitive allocation/capacity/KMX value-frame/copy induction/set_len/nine return frames; NHJ_EntryDomains derives every actual caller bound','error.clone':'sole ABF domain derived by SDK error arm; NHD_K014/015 and NGL_CloneDomain.clone, NHY_SnapshotHeader.clone_reply'}
for rid in ['TX1:343','TX2:239']:
 r=copy.deepcopy(by[rid]);assert r['composed_status']=='OPEN'
 r.update(composed_status='CLOSED',bridge_status='CLOSED-CONDITIONAL',selected_claims=['NHY::snapshot'],active_support_receipts=[str((E/a/'receipt.json').relative_to(R)) for a in ['NHY_K005','NHY_K006','NHY_K008','NHY_K009']],open_transitive_dependencies=[],composed_reason='Complete staged snapshot native/model packet; root borrow success derived from accepted SDK15 at computed Entry.heap, both legal Result arms retained before root specialization.')
 for o in r['caller_domain_obligations']:
  expression=o['call'].get('expression',o['call'].get('name'));expression={'try_borrow_data':'account.try_borrow_data','len':'data.len','to_vec':'data.to_vec','clone':'error.clone'}.get(expression,expression);assert expression in reasons or expression in ['Ok','Err'],expression
  o.update(status='CLOSED',discharged_by='NHY::snapshot: '+reasons.get(expression,'Actual constructor arms/metadata K005/K006, generic Header/finish chain'))
 for h in r['named_hypotheses']:raise AssertionError('unexpected named hypothesis requires explicit review')
 assert not n.row_checks(r,by[rid],cert);rows.append(r);certs[rid]=cert;candidates[rid]=('NHY',r)
n.certificate_checks(type('Support',(),{'support':lambda self,c:None})(),cert)
tiny=copy.deepcopy(base);tiny['rows']=[copy.deepcopy(by[rid]) for rid in candidates]
admitted=n.admit(tiny,candidates,certs,{'NHY':list(candidates)});assert all(r['composed_status']=='CLOSED' for r in admitted['rows'])
for rid,r in ((r['row'],r) for r in rows):
 bad=copy.deepcopy(r);bad['frozen_body_sha256']='0'*64;assert 'candidate frozen identity mismatch' in n.row_checks(bad,by[rid],cert)
 bad=copy.deepcopy(r);bad['caller_domain_obligations'][0]['status']='OPEN';assert 'Open caller-domain obligation' in n.row_checks(bad,by[rid],cert)
try:n.certificate_checks(type('Support',(),{'support':lambda self,c:None})(),dict(inner_hypotheses_remaining=['unpaired SDK stub']))
except ValueError:pass
else:raise AssertionError('residual inner hypothesis accepted')
assert lzma.decompress(basepath.read_bytes())==data
put('NHY_CLOSED.json',dict(schema_version=1,frozen_revision=base['frozen_revision'],new_composed_functions=1,new_composed_rows=2,functions=[cert],driver_root_status='OPEN'))
put('NHY_EDGES.json',dict(edges=[o for r in rows for o in r['caller_domain_obligations']],no_out_of_slice_credit=True))
put('NHY_LEDGER_DELTA.json',dict(baseline=str(basepath.relative_to(R)),baseline_uncompressed_sha256=sha(data),new_closed_rows=list(candidates),rows=rows,no_other_status_change=True,validator_checks_added_only=True,unchanged_NFK_validator_sha256=pin,checks_added=['admission exit0 AND allowed:true, exact caps and source snapshots','per-run frozen graph, lock, offline, deployed features and exact KMX','both explicit SDK arms; canonical clone domain; no writable static/custom copy stub','same-entry SDK-derived root acquisition, all-length scalar dispatch, full Header/finish chain and caller table bounds','NGK/RPx combined, ax2 identical walker/eight fixtures/same binary/standard axioms; NFX zero defects','unchanged NFK row/certificate/admit checks; five denial mutations'],whole_ledger_counts_after=dict(total=599,CLOSED=337,OPEN=262),baseline_preserved_byte_exactly=True,mutation_denials=5,trust_reclassification='Retained P6/D188 option A; nothing removed or newly adopted',inherited_NHJ_delta='Separate immutable14-row delta, not duplicated in NHY new rows'))
put('NHY_AUDIT.json',dict(status='PASS_AX2_NFX',combined='NHY_L010',roots=[r for p in proofs for r in p['results']],fixtures=fx,scan=scan,walker_sha256=sha((P/'NGL_WALKER_SOURCE.lean.txt').read_bytes()),driver_diffs=['NHY_ProofDriver.diff','NHY_ScanDriver.diff'],scope='Focused coherent cached replay, not cold release manifest',standard_axioms_only=True))
put('NHY_LOCAL_VALIDATION.json',dict(target='NHY_certify snapshot two-row admission',exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//(1024 if sys.platform=='darwin' else 1),swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=sha(Path(__file__).read_bytes()),print_axioms='N/A Python evidence validation; exact formal audits in NHY_AUDIT.json',new_closed_rows=2))
print(json.dumps(dict(status='PASS',new_closed_rows=2)))
