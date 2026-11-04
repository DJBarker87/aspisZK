#!/usr/bin/env python3
"""Additive NFQ/NFK certificate admission. No inherited check is weakened."""
import pathlib,sys,json,lzma,hashlib,importlib.util,re,copy,subprocess,collections
sys.dont_write_bytecode=True
E=pathlib.Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
J=lambda n:json.loads((E/n).read_text())
sp=importlib.util.spec_from_file_location('NFU_NFQ',R/'evidence/slice-d-define-20261104/NFQ_certify.py');NFQ=importlib.util.module_from_spec(sp);sp.loader.exec_module(NFQ)
NFK=NFQ.NFK
base=json.loads(lzma.decompress((R/'evidence/slice-d-define-20261104/NFQ_COMPOSED_LEDGER.json.xz').read_bytes()));NFK.BASE_CREDITS=base['NEZ_credits']
by={r['row']:r for r in base['rows']};functions={r['function']:r for r in NFQ.order['functions']}
standard={'propext','Classical.choice','Quot.sound'}
def put(n,v):(E/n).write_text(json.dumps(v,indent=1)+'\n')
def native(k,expected):
 a=f'NFU_K{k:03}';r=J(a+'/receipt.json');ad=J(a+'-admission.json')
 assert r['exit_status']==expected and ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and int(r['swaps'])==0
 assert J(a+'-graph-check.json')['graph_matches_frozen'] and J(a+'-lock-check.json')==dict(before='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',after='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',unchanged=True)
 assert not J(a+'-source-check.json')['errors']
 assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 text=(E/a/'stdout.log').read_text();assert 'VERIFICATION:- '+('FAILED' if expected else 'SUCCESSFUL') in text
 if expected:assert re.search(r'\*\* 1 of \d+ failed',text)
 return r,text

def audited():
 result={}
 for directory,modes in [('NFU_final_audit',['proof0']),('NFU_stage2_audit',[f'stage2proof{i}'for i in range(19)])]:
  assert J(directory+'/SUMMARY.json')['status']=='PASS'
  NFK.fixtures(J(directory+'/fixtures.json')['results'])
  for mode in ['fixtures']+modes:
   rc=J(directory+'/'+mode+'.json');assert rc['exit_status']==0 and int(rc['swaps'])==0
   if mode=='fixtures':continue
   for x in rc['results']:
    assert x['equal'] and set(x['collect_axioms'])==set(x['walked_axioms'])<=standard
    result[x['root']]=x
 assert set(J('NFU_STAGE2_ROOTS.json'))<=result.keys()
 assert J('NFU_RETARGET_CHECK.json')['status']=='PASS'
 assert (E/'NFU_WALKER_SOURCE.lean.txt').read_bytes()==(R/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes()
 return result

def pins(names):return [dict(path=str((E/n).relative_to(R)),sha256=sha((E/n).read_bytes())) for n in names]
def build():
 roots=audited();certs={};candidates={};closed=[];edges=[]
 for k,e in [(9,0),(10,1),(11,1)]:native(k,e)
 assert 'is assignable' in (E/'NFU_K011/stdout.log').read_text()
 for method,p,n,root,domain in [('row',12,13,'NFU_RecordGetters.row','All u8 row values; SAME valid typed framed slice length 0..3717; no token-validation or canonicality precondition'),('framed',3,4,'NFU_RecordGetters.framed','All u8 row values; SAME valid typed framed slice length 0..3717; arbitrary start/content; complete borrowed return identity')]:
  f="crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::"+method
  assert f in functions and root in roots
  a,_=native(p,0);b,_=native(n,1);assert a['module']==b['module']
  source=E/'NFU_RecordGetters.lean';matches=[J(str(q.relative_to(E))) for q in E.glob('NFU_L???/receipt.json') if json.loads(q.read_text())['exit_status']==0 and json.loads(q.read_text())['module']=='NFU_RecordGetters']
  assert any(sha(source.read_bytes()) in q['source_hashes'].values() for q in matches)
  assert not functions[f]['callees']
  physical='Retained root carrier/ABI, frozen source/features/compiler/library/source-to-ELF and P6/D188 option A native contract semantic transport; reclassification, not removal'
  row=dict(function=f,rows=functions[f]['rows'],status='CLOSED',form='ruling (y)/(y\') hybrid',domain=domain,native_positive=f'NFU_K{p:03}',matched_control=f'NFU_K{n:03}',lean_root=root,model_association='Actual emitted PublicPreparation getter; NFU_RecordGetters parser getter and same_token laws preserve both original fields',axioms=roots[root]['walked_axioms'],frame='No mutation, allocation, cleanup, callback, digest, oracle or protocol event; row contract empty modifies; framed returns exact same typed pointer and length from immutable borrow',KMX='Not needed: asserted scalar/provenance/length properties depend on no reached copy builtin',inner_hypotheses_remaining=[])
  closed.append(row)
  for rid in row['rows']:
   r=by[rid];file=f.split('::')[0];raw=subprocess.check_output(['git','show',base['frozen_revision']+':'+file],cwd=R);start,end=r['frozen_body_byte_range'];body=raw[start:end];assert sha(body)==r['frozen_body_sha256']
   for k in [p,n]:assert body in (E/f'NFU_K{k:03}/sources/NFU_src'/file).read_bytes()
   support=[f'NFU_K{k:03}/{z}' for k in [p,n] for z in ['receipt.json','stdout.log']]+['NFU_RecordGetters.lean','NFU_final_audit/proof0.json','NFU_DRIVER.diff']
   cert=NFQ.seal(dict(id='NFU::'+rid,row=rid,subject=f,function=f,frozen_body_sha256=r['frozen_body_sha256'],domain=domain,top_hypotheses=[physical],inner_hypotheses_remaining=[],native=row,external_obligations={o['id']:dict(classification='Exact immutable field projection and complete borrowed return on SAME typed record',detail=o['call']) for o in r['caller_domain_obligations'] if 'callee' not in o},support=pins(support)))
   NFK.certificate_checks(NFQ.Support(),cert);candidate=NFK.materialize_recipe(r,cert,'NFU',{'edges':edges});assert not NFK.row_checks(candidate,r,cert);candidates[rid]=('NFU',candidate);certs[rid]=cert
 # Additional complete packets, admitted by the same unchanged NFK engine.
 extra=[
  ('programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key',16,17,'NFU_AdapterGetters.key','All valid borrowed account keys; complete SAME typed Pubkey borrow; other fields unread',[],[]),
  ('programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::owner',18,19,'NFU_AdapterGetters.owner','All valid borrowed owner keys; complete SAME typed Pubkey borrow; other fields unread',[],[]),
  ('programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer',22,23,'NFU_AdapterGetters.readonly','All three metadata flags; all unread keys/owner/deferred-error/buffer fields; complete ProgramResult',[],[]),
  ('crates/aspis-r1-cost-probe/src/compact.rs::check_values',32,33,'NFU_CompactLeaves.check_result','SAME 464-byte adopted y1 window; arbitrary bytes and every rejected prefix; no canonicality premise',[(30,31)],[(40,41)]),
  ('crates/aspis-r1-cost-probe/src/compact.rs::expand_values',26,27,'NFU_CompactLeaves.expand_result','All input lengths0..1856/output lengths0..3712, arbitrary values, SAME unique borrowed output; complete guards and one-window/frame induction',[(28,29),(38,39)],[(24,25)]),
  ('crates/aspis-r1-cost-probe/src/r1_wire.rs::validate_record_fields',34,35,'NFU_CompactLeaves.validate_result','Every row u8, payload length0..3712, arbitrary canonical/noncanonical bytes, ignored tails, exact first-error usize index',[(36,37)],[(40,41)]),
  ("crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::record",64,65,'NFU_PrefixRecords.record','Every row u8 and 27 valid framed slices of length0..3717; SAME selected immutable typed slice, every InvalidRow; c1 root unread',[],[(64,65)]),
  ("crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::validated_record",66,67,'NFU_PrefixRecords.validated_record','SAME Prefix/row domain as record; exact row and SAME selected slice or unchanged error; no new token-validity claim',[],[(66,67)]),
  ('programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_zero',68,69,'NFU_ZeroPort.source','SAME valid immutable allocation, length0..4096, all bytes and every arbitrary tail pre-state, all rejected prefixes; no accepted/all-zero premise',[],[])]
 for f,p,n,root,domain,steps,copies in extra:
  assert f in functions and root in roots
  a,_=native(p,0);b,_=native(n,1);assert a['module']==b['module']
  for positive,negative in steps+copies:
   aa,_=native(positive,0);bb,_=native(negative,1);assert aa['module']==bb['module']
  if copies:assert sha((R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes())=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  module=root.rsplit('.',1)[0];source=E/(module+'.lean');assert source.exists()
  matched=[json.loads(q.read_text())for q in E.glob('NFU_L???/receipt.json')if json.loads(q.read_text())['exit_status']==0 and json.loads(q.read_text())['module']==module and sha(source.read_bytes())in json.loads(q.read_text())['source_hashes'].values()];assert matched,root
  child=[]
  for callee in functions[f]['callees']:
   target=callee['function'];assert target in {x['function']for x in closed} or all(by[r]['composed_status']=='CLOSED'for r in callee['rows']),(f,target)
   if f.endswith('::check_values'):reason='Actual chunks_exact16 iterator K030 selects SAME 16-byte y1 window; arbitrary bytes accepted by QM31 decoder packet. NFU_Retarget.LPl.Check.window/chunk_eq/stage and native K032 preserve decoder Result on that exact window, including rejection; no product/canonical-input restriction.'
   elif f.endswith('::validate_record_fields'):reason='K036 actual enumeration establishes SAME32-byte window and current i<116; K034 is the verbatim source callback on arbitrary row/current i. WideExact decoder packet covers every32-byte array; its returned eight-limb record lies in NFQ c1 getter all-raw-limb domain. NFU_Retarget.LPl.Validate.window/native_result/error_bound preserve exact first error and usize port.'
   elif f.endswith('::require_readonly_buffer'):reason='The frozen caller forwards exactly its original three Bool fields, each in NFQ readonly_buffer_meta_ok universal Bool domain. NFU_AdapterGetters.readonly/frame instantiate the CLOSED NFQ callee; real body executes natively.'
   elif f.endswith('::validated_record'):reason='The exact SAME Prefix and row are forwarded to record, with no prior change. Its domain is identical; NFU_PrefixRecords.validated_record substitutes that SAME reply and preserves every error and both token fields. No independently chosen token or accepted output is assumed.'
   else:raise AssertionError((f,target))
   edge=dict(edge=f+' -> '+target,status='CLOSED',certificate=dict(native=f'NFU_K{p:03}',lean_root=root,domain_proof=reason,callee_packets=callee['existing_packets']));edges.append(edge);child.append(edge)
  frame='Read-only input/account frame, complete Result and SAME returned borrowed carrier; no allocation, cleanup, callback, digest/oracle/protocol event'
  association='Exact emitted source helper plus NFU field-irrelevance/domain laws on the SAME input'
  if 'compact.rs::expand_values' in f:
   frame='Complete SAME mutable output; all guard errors unchanged; one exact KMX low16 write/high16 fill with arbitrary point frame, full source zip iterator; NFU_Retarget.LPn.Expand local_global/write_of_observations/NativeTrace/native_result and length_error compose all windows, including empty'
   association='Retained CLOSED LPn opaque leaf, private namespace only; exact type/constructor value ports; complete byte Result/frame/trace'
  elif 'compact.rs::check_values' in f or f.endswith('::validate_record_fields'):
   association='Retained CLOSED LPl opaque leaf, private namespace only; complete first-error source-order Scan.Trace and exact scalar/error ports; native callback+iterator association'
  elif f.endswith('::require_zero'):
   frame='No source byte write or escape. K068 one cut covers all lengths/tail displacements within4096 and arbitrary observed frame byte, exact done/reject/next Result, SAME pointer and successor length; source literal while loop has no other effect'
   association='Invariant: current tail=original.drop i, ptr=base+i, remaining=length-i. NFU_ZeroPort.head/length/advance/index_advance associate both native cuts to NFQ_ZeroStep.zero_step/reject_step; empty tail is indexed-loop terminal. NFQ_ZeroReference.loop_reference is the full decreasing-remaining induction; NFQ_ZeroSource.source gives exact source/reference Result, including every rejected prefix. No final-output/accepted-run premise.'
  row=dict(function=f,rows=functions[f]['rows'],status='CLOSED',form='ruling (y)/(y\') hybrid; one-iteration induction where needed',domain=domain,native_positive=f'NFU_K{p:03}',matched_control=f'NFU_K{n:03}',additional_pairs=steps,copy_pairs=copies,lean_root=root,model_association=association,axioms=roots[root]['walked_axioms'],internal_edges=child,frame=frame,KMX=None if not copies else 'Exact adopted patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67; listed matched copy controls',inner_hypotheses_remaining=[])
  closed.append(row)
  for rid in row['rows']:
   r=by[rid];file=f.split('::')[0];raw=subprocess.check_output(['git','show',base['frozen_revision']+':'+file],cwd=R);start,end=r['frozen_body_byte_range'];body=raw[start:end];assert sha(body)==r['frozen_body_sha256']
   for k in [p,n]:assert body in (E/f'NFU_K{k:03}/sources/NFU_src'/file).read_bytes()
   if f.endswith('::validate_record_fields'):
    step=J('NFU_VALIDATOR_STEP_SOURCE.json');lo,hi=step['byte_range'];assert raw[lo:hi].decode()==step['actual_iteration_body']
   support=[f'NFU_K{k:03}/{z}'for k in sorted({p,n}|{k for pair in steps+copies for k in pair})for z in ['receipt.json','stdout.log']]+[module+'.lean','NFU_RETARGET_CHECK.json','NFU_STAGE2_DRIVER.diff']
   if f.endswith('::validate_record_fields'):support+=['NFU_VALIDATOR_STEP_SOURCE.json']
   cert=NFQ.seal(dict(id='NFU::'+rid,row=rid,subject=f,function=f,frozen_body_sha256=r['frozen_body_sha256'],domain=domain,top_hypotheses=[physical],inner_hypotheses_remaining=[],native=row,external_obligations={o['id']:dict(classification=frame,detail=o['call'])for o in r['caller_domain_obligations']if 'callee'not in o},support=pins(support)))
   NFK.certificate_checks(NFQ.Support(),cert);candidate=NFK.materialize_recipe(r,cert,'NFU',{'edges':edges})
   for ob in candidate['caller_domain_obligations']:
    if 'callee'in ob:
     if ob['callee']in {x['function']for x in closed}:ob['callee_claims']=['NFU::'+ob['callee']]
     elif any(x['function']==ob['callee']for x in json.loads((R/'evidence/slice-d-define-20261104/NFQ_CLOSED.json').read_text())['functions']):ob['callee_claims']=['NFQ::'+ob['callee']]
   assert not NFK.row_checks(candidate,r,cert);candidates[rid]=('NFU',candidate);certs[rid]=cert
 out=NFK.admit(base,candidates,certs,{'NFU':sorted(candidates)});outby={r['row']:r for r in out['rows']};assert all(outby[r]['composed_status']=='CLOSED' for r in candidates)
 assert all(outby[r['row']]['composed_status']==r['composed_status'] for r in base['rows'] if r['row'] not in candidates)
 # Inherited rejection invariants must continue to reject broken candidates.
 tests=[];rid=next(iter(candidates))
 for name,mutate in [('wrong frozen body',lambda x:x.update(frozen_body_sha256='0'*64)),('undischarged domain',lambda x:x['named_hypotheses'][0].update(discharged_by=None)),('open child',lambda x:x.update(open_transitive_dependencies=['missing'])),('no selected claim',lambda x:x.update(selected_claims=[]))]:
  bad=copy.deepcopy(candidates[rid][1]);mutate(bad);assert NFK.row_checks(bad,by[rid],certs[rid]);tests.append(name)
 for name,mutate in [('changed certificate',lambda x:x.update(domain='altered')),('hidden inner premise',lambda x:x.update(inner_hypotheses_remaining=['missing']))]:
  bad=copy.deepcopy(certs[rid]);mutate(bad)
  try:NFK.certificate_checks(NFQ.Support(),bad)
  except (AssertionError,ValueError):tests.append(name)
  else:raise AssertionError(name)
 put('NFU_CERTIFICATES.json',certs);put('NFU_EDGES.json',edges)
 put('NFU_CLOSED.json',dict(schema_version=1,frozen_revision=base['frozen_revision'],new_composed_functions=len(closed),new_composed_rows=len(candidates),driver_root_status='OPEN',functions=closed))
 put('NFU_LEDGER_DELTA.json',dict(baseline='evidence/slice-d-define-20261104/NFQ_COMPOSED_LEDGER.json.xz',new_closed_rows=sorted(candidates),new_count=len(candidates),D_counts_after=dict(total=343,CLOSED=21+len(candidates),OPEN=322-len(candidates)),no_other_status_change=True,not_a_premise_retirement=True,trust_reclassification='P6/D188 option A retained; not removed',rows=[dict(row=r,function=by[r]['function'],before='OPEN',after='CLOSED')for r in sorted(candidates)]))
 put('NFU_AUDIT.json',dict(status='PASS for 11 composed functions / 14 new D rows; driver OPEN',raw_roots=roots,standard_axioms_only=True,walker_sha256=sha((E/'NFU_WALKER_SOURCE.lean.txt').read_bytes()),raw_audit='NFU_L005 and NFU_L059',fixtures='same adapted driver, eight expected results',NFQ_validator_sha256=sha((R/'evidence/slice-d-define-20261104/NFQ_certify.py').read_bytes()),unchanged_NFK_validator_sha256=sha((R/'evidence/ledger6-20261104/NFK_validate.py').read_bytes()),mutation_tests=tests,excluded=['K001/K002 narrower row diagnostic superseded by K012/K013 full framed domain','L006 failed row bound elaboration; excluded; repaired in L007','K005/K006 payload helper not an assigned inventory occurrence','K007/K008 pre-KMX diagnostics superseded by K032/K033','K014/K020 metadata general-enum equality timeouts','K050/K052 parser-tail timeouts; guarded fragments K015/K063 and K021/K053 do not close parsers','K062 own Prefix harness type error','L008/L010/L013/L046/L055 failed elaborations and L047 charged prelaunch failure','E001..E003 safe reference extraction only; full carrier/model association OPEN']))
 raw=json.dumps(out,indent=1).encode();(E/'NFU_COMPOSED_LEDGER.json.xz').write_bytes(lzma.compress(raw));(E/'NFU_COMPOSED_LEDGER.json.sha256').write_text(sha(raw)+'\n')
 print(json.dumps(dict(valid=True,new_functions=len(closed),new_rows=len(candidates),remaining_D_rows=322-len(candidates))))
if __name__=='__main__':build()
