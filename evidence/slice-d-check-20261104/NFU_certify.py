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
 assert J('NFU_final_audit/SUMMARY.json')['status']=='PASS'
 fx=J('NFU_final_audit/fixtures.json');NFK.fixtures(fx['results'])
 for n in ['fixtures','proof0']:
  rc=J('NFU_final_audit/'+n+'.json');assert rc['exit_status']==0 and int(rc['swaps'])==0
 roots=J('NFU_final_audit/proof0.json')['results']
 assert all(x['equal'] and set(x['collect_axioms'])==set(x['walked_axioms'])<=standard for x in roots)
 assert (E/'NFU_WALKER_SOURCE.lean.txt').read_bytes()==(R/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes()
 return {x['root']:x for x in roots}

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
 put('NFU_AUDIT.json',dict(status='PASS for admitted getter rows; other members pending',raw_roots=roots,standard_axioms_only=True,walker_sha256=sha((E/'NFU_WALKER_SOURCE.lean.txt').read_bytes()),raw_audit='NFU_L005',fixtures='same adapted driver, eight expected results',NFQ_validator_sha256=sha((R/'evidence/slice-d-define-20261104/NFQ_certify.py').read_bytes()),unchanged_NFK_validator_sha256=sha((R/'evidence/ledger6-20261104/NFK_validate.py').read_bytes()),mutation_tests=tests,excluded=['K001/K002 narrower row diagnostic superseded by K012/K013 full framed domain','L006 failed row bound elaboration; excluded; repaired in L007','K005/K006 payload helper not an assigned inventory occurrence','K007/K008 one-chunk canonicality only; no complete-loop closure']))
 raw=json.dumps(out,indent=1).encode();(E/'NFU_COMPOSED_LEDGER.json.xz').write_bytes(lzma.compress(raw));(E/'NFU_COMPOSED_LEDGER.json.sha256').write_text(sha(raw)+'\n')
 print(json.dumps(dict(valid=True,new_functions=len(closed),new_rows=len(candidates),remaining_D_rows=322-len(candidates))))
if __name__=='__main__':build()
