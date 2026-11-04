#!/usr/bin/env python3
"""Add checks only: unchanged NFK admission, plus NFQ full-certificate gates."""
import json,pathlib,hashlib,re,copy,lzma,sys,importlib.util,collections,subprocess
sys.dont_write_bytecode=True
E=pathlib.Path(__file__).resolve().parent;R=E.parents[1]
J=lambda n:json.loads((E/n).read_text())
sha=lambda x:hashlib.sha256(x).hexdigest()
standard={'propext','Classical.choice','Quot.sound'}
sp=importlib.util.spec_from_file_location('NFQ_pinned_NFK',R/'evidence/ledger6-20261104/NFK_validate.py');NFK=importlib.util.module_from_spec(sp);sp.loader.exec_module(NFK)
base=json.loads(lzma.open(R/'evidence/ledger6-20261104/NFK_LEDGER.json.xz').read());NFK.BASE_CREDITS=base['NEZ_credits']
by={r['row']:r for r in base['rows']};order=J('NFQ_ORDER.json');functions={r['function']:r for r in order['functions']}
F='crates/aspis-core/src/field.rs::';V='crates/aspis-r1-cost-probe/src/';T='crates/aspis-statement/src/'
# Native gates always execute the real callee bodies. No stub_verified use occurs
# in any credited body proof. Separate fidelity controls are diagnostic support.
specs=[
 (order['first_five'][0],2,3,'NFQ_RowShape.compact_reference','all u8',None,'NFQ_E001'),
 (order['first_five'][1],4,5,'NFQ_RowShape.reference','all u8',None,'NFQ_E001'),
 (order['first_five'][2],6,7,'NFQ_Transport.folds_reference','all three native Variant constructors',None,'NFQ_E001'),
 (order['first_five'][3],8,9,'NFQ_Transport.final_len_reference','all three native Variant constructors',None,'NFQ_E001'),
 (order['first_five'][4],10,11,'NFQ_Transport.checkpoint_size_reference','all three native Variant constructors',None,'NFQ_E001'),
 ('programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_buffer_meta_ok',19,20,'NFQ_Readonly.reference','all three boolean flags; full ProgramResult including exact error',None,'NFQ_E003'),
 (F+'M31::neg',21,22,'NFQ_FieldLaws.neg_value','one canonical limb x<P',None,'existing emitted field model; NFQ_FieldPorts.sampler_neg'),
 (F+'CM31::from_m31',23,24,'NFQ_FieldLaws.cm_reference','all raw u32 inputs',None,'existing emitted field model; NFQ_FieldPorts.fiq_cm'),
 (F+'QM31::from_cm31',25,26,'NFQ_FieldLaws.qm_reference','all two raw u32 limbs',None,'existing emitted field model; NFQ_FieldPorts.fiq_qm'),
 (F+'M31::reduce_u62',29,30,'NFQ_Reduce.source','all u64 values below 2^62 (documented source precondition)',None,'existing emitted reducer and current_reduce_mod'),
 (F+'PreparedQm31Multiplier::new',31,32,'NFQ_PreparedMultiplier.source','four canonical u32 limbs; full nine-word result',(27,28),'existing emitted field model and complete natural spec; NFQ_PreparedDomain.output_domain'),
 (T+'pool_v1/pair_forest_semantic_terminal.rs::variant_expected_output',33,34,'NFQ_StatementLaws.expected_reference','both valid CompiledVariant constructors',None,'existing emitted FIq_Native function'),
 (T+'pool_v1/pair_forest_semantic_terminal.rs::copy_variant',35,36,'NFQ_StatementLaws.copied_reference','both valid CompiledVariant constructors',None,'existing emitted FIq_Native function'),
 (T+'state_only_poseidon.rs::extension_limbs',37,38,'NFQ_StatementLaws.limbs_reference','all four raw u32 limbs; full four-word array',(39,40),'existing emitted FIq_Native function'),
 ('crates/aspis-core/src/field/wide_exact.rs::WideExact::c0',54,55,'NFQ_WideGetters.c0','all eight raw u32 limbs; full returned four-word record',(52,53),'existing CurrentWide/loaded FIo record projection; NBG_GetterPorts port shape, revalidated with two inverse laws'),
 ('crates/aspis-core/src/field/wide_exact.rs::WideExact::c1',56,57,'NFQ_WideGetters.c1','all eight raw u32 limbs; full returned four-word record',(52,53),'existing CurrentWide/loaded FIo record projection; NBG_GetterPorts port shape, revalidated with two inverse laws')]

def native(k,exit):
 r=J(f'NFQ_K{k:03}/receipt.json');a=J(f'NFQ_K{k:03}-admission.json')
 assert r['exit_status']==exit and a['exit']==0 and a['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and int(r['swaps'])==0
 g=J(f'NFQ_K{k:03}-graph-check.json');l=J(f'NFQ_K{k:03}-lock-check.json');sc=J(f'NFQ_K{k:03}-source-check.json')
 assert g['graph_matches_frozen'] and l['unchanged'] and l['before']==l['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef' and not sc['errors']
 assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 s=(E/f'NFQ_K{k:03}/stdout.log').read_text();assert 'VERIFICATION:- '+('FAILED' if exit else 'SUCCESSFUL') in s
 if exit:assert re.search(r'\*\* 1 of \d+ failed',s)
 return r,s

def pair(p,n):
 a,_=native(p,0);b,s= native(n,1)
 assert 'cfg!(NFQ_invert)' in s and 'Failed Checks: |r|' in s
 assert a['module']==b['module']
 return a,b

def audit():
 result={}
 for directory,modes in [('NFQ_final_audit',['proof0','proof1']),('NFQ_stage2_audit',[f'stage2proof{i}' for i in range(5)])]:
  assert J(directory+'/SUMMARY.json')['status']=='PASS'
  for mode in modes:
   r=J(directory+'/'+mode+'.json');assert r['exit_status']==0 and int(r['swaps'])==0
   for x in r['results']:
    assert x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<=standard
    result[x['root']]=x
  NFK.fixtures(J(directory+'/fixtures.json')['results'])
 assert set(J('NFQ_STAGE2_ROOTS.json'))<=result.keys()
 assert (E/'NFQ_WALKER_SOURCE.lean.txt').read_bytes()==(R/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes()
 return result

class Support:
 def support(self,certificate):
  for item in NFK.walk(certificate):
   if isinstance(item,dict) and {'path','sha256'}<=item.keys():assert sha((R/item['path']).read_bytes())==item['sha256']

def pins(names):return [dict(path=str((E/n).relative_to(R)),sha256=sha((E/n).read_bytes())) for n in names]
def seal(c):c['semantic_review_sha256']=sha(json.dumps(c,sort_keys=True).encode());return c

def build():
 audited=audit();closed=[];candidates={};certs={};edges=[]
 for real,unimplied,frame in [(13,14,15),(16,17,18),(41,42,43),(44,45,46),(47,48,49)]:
  native(real,0)
  _,text=native(unimplied,1);assert ('core::panicking::assert_failed_inner' in text if unimplied in [14,17] else {42:'assertion failed: matches!(weak_enum()',45:'assertion failed: weak_array()[1] == 1',48:'assertion failed: weak_prepared().components[1][1].0 == 4'}[unimplied] in text)
  _,text=native(frame,1);assert 'is assignable' in text
 for f,p,n,root,domain,kmx,model in specs:
  a,b=pair(p,n);assert root in audited and f in functions
  if kmx:
   native(kmx[0],0);native(kmx[1],1)
   assert sha((R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes())=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  module=root.rsplit('.',1)[0];source=E/(module+'.lean')
  # Every credited theorem has a successful focused compile of these exact bytes.
  matching=[]
  for rr in E.glob('NFQ_L???/receipt.json'):
   q=json.loads(rr.read_text())
   if q['exit_status']==0 and q['module']==module and sha(source.read_bytes()) in q['source_hashes'].values():matching.append(q)
  assert matching,root
  frame='empty modifies; complete return value; no mutable argument, callback, event, oracle call or writable static'
  child=[]
  for c in functions[f]['callees']:
   target=c['function'];excluded=f==F+'PreparedQm31Multiplier::new' and target in [F+'QM31::add','crates/aspis-core/src/field/wide_exact.rs::WideExact::add']
   if excluded:
    reason='Static receiver resolution: value.c0/value.c1 and c0+c1 are CM31; closure c.a+c.b is M31. No QM31 or WideExact addition is called. Frozen body and typed actual native contract execute this same closure.'
   elif f==F+'PreparedQm31Multiplier::new':reason='CanonicalQM establishes both CM inputs; current_cm_add_mod proves their sum canonical. row_source uses canonical inputs and current_add_mod for all three scalar sums. Actual native add bodies execute, without substitution.'
   elif f==F+'M31::reduce_u62':reason='reduce_u64 domain is all u64; incoming bound<2^62 is a subset; NFQ_Reduce.source invokes current_reduce_mod with exactly the same value; native real callee executes.'
   else:reason='All native Variant constructors preserved unchanged; real callee executes; same fieldless constructor map used by NFQ_Transport.'
   if not excluded:assert target in {x[0] for x in specs} or all(by[r]['composed_status']=='CLOSED' for r in c['rows'])
   e=dict(edge=f+' -> '+target,status='CLOSED',certificate=dict(native=f'NFQ_K{p:03}',lean_root=root,domain_proof=reason,selected=not excluded,callee_packets=c['existing_packets']))
   edges.append(e);child.append(e)
  cc=dict(function=f,rows=functions[f]['rows'],status='CLOSED',form='ruling (y) hybrid',domain=domain,native_positive=f'NFQ_K{p:03}',matched_control=f'NFQ_K{n:03}',lean_root=root,model_association=model,axioms=audited[root]['walked_axioms'],internal_edges=child,frame=frame,KMX=None if not kmx else dict(patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',positive=f'NFQ_K{kmx[0]:03}',negative=f'NFQ_K{kmx[1]:03}'),physical_interpretation='Root-retained same carrier/ABI, pinned frozen source/features, compiler/library/source-to-ELF and P6/D188 native contract semantic transport (option A); no premise retired',inner_hypotheses_remaining=[])
  closed.append(cc)
  for rid in cc['rows']:
   r=by[rid]
   source_file=r['function'].split('::')[0]
   frozen=subprocess.check_output(['git','show',base['frozen_revision']+':'+source_file],cwd=R)
   start,end=r['frozen_body_byte_range'];frozen_body=frozen[start:end]
   assert sha(frozen_body)==r['frozen_body_sha256']
   for k in [p,n]:
    snapshot=E/f'NFQ_K{k:03}/sources/NFQ_src'/source_file
    assert frozen_body in snapshot.read_bytes(),('frozen body changed',rid,k)
   support=[f'NFQ_K{k:03}/{x}' for k in [p,n] for x in ['receipt.json','stdout.log']]+[module+'.lean']
   cert=seal(dict(id='NFQ::'+rid,row=rid,subject=f,function=f,frozen_body_sha256=r['frozen_body_sha256'],domain=domain,top_hypotheses=[cc['physical_interpretation']],inner_hypotheses_remaining=[],native=cc,external_obligations={o['id']:dict(classification='pure enum/scalar/inline closure; exact complete typed body included in native contract and emitted reference equation',detail=o['call']) for o in r['caller_domain_obligations'] if 'callee' not in o},support=pins(support)))
   NFK.certificate_checks(Support(),cert)
   candidate=NFK.materialize_recipe(r,cert,'NFQ',{'edges':edges})
   for ob in candidate['caller_domain_obligations']:
    if 'callee' in ob:
     edge=next(e for e in child if e['edge']==f+' -> '+ob['callee'])
     if not edge['certificate']['selected']:ob['callee_claims']=[]
     elif ob['callee'] in {x[0] for x in specs}:ob['callee_claims']=['NFQ::'+ob['callee']]
   assert not NFK.row_checks(candidate,r,cert)
   candidates[rid]=('NFQ',candidate);certs[rid]=cert
 out=NFK.admit(base,candidates,certs,{'NFQ':sorted(candidates)})
 outby={r['row']:r for r in out['rows']};assert all(outby[r]['composed_status']=='CLOSED' for r in candidates)
 assert len(candidates)==21 and len(closed)==16
 for r in base['rows']:
  if r['row'] not in candidates:assert outby[r['row']]['composed_status']==r['composed_status']
 # Preserve original gates; demonstrate denial of malformed candidates as well.
 tests=[];rid=next(iter(candidates));candidate=candidates[rid][1];cert=certs[rid]
 for name,mutate in [('frozen body',lambda x:x.update(frozen_body_sha256='0'*64)),('missing hypothesis',lambda x:x['named_hypotheses'][0].update(discharged_by=None)),('open dependency',lambda x:x.update(open_transitive_dependencies=['missing'])),('missing selected claim',lambda x:x.update(selected_claims=[]))]:
  bad=copy.deepcopy(candidate);mutate(bad);assert NFK.row_checks(bad,by[rid],cert);tests.append(name)
 for name,change in [('review digest',lambda c:c.update(domain='changed')),('inner hypothesis',lambda c:c.update(inner_hypotheses_remaining=['not discharged']))]:
  bad=copy.deepcopy(cert);change(bad)
  try:NFK.certificate_checks(Support(),bad)
  except (ValueError,AssertionError):tests.append(name)
  else:raise AssertionError(name)
 out['NFQ_owner_trust_amendment']={'date':'2026-11-04','RuntimeReturnData':'ACCEPTED retained trust; not discharged','RuntimeMemcmp':'ACCEPTED retained trust; not discharged','historical_NFK_pending_wording':'Superseded by owner decision, without altering the unchanged NFK validator'}
 raw=json.dumps(out,indent=1).encode();(E/'NFQ_COMPOSED_LEDGER.json.xz').write_bytes(lzma.compress(raw));(E/'NFQ_COMPOSED_LEDGER.json.sha256').write_text(sha(raw)+'\n')
 def put(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
 put('NFQ_CERTIFICATES.json',certs);put('NFQ_EDGES.json',edges)
 put('NFQ_CLOSED.json',dict(schema_version=1,frozen_revision=base['frozen_revision'],new_composed_functions=16,new_composed_rows=21,driver_root_status='OPEN',functions=closed))
 counts=dict(collections.Counter(r['composed_status'] for r in out['rows']))
 put('NFQ_LEDGER_DELTA.json',dict(baseline='evidence/ledger6-20261104/NFK_LEDGER.json.xz',frozen_revision=base['frozen_revision'],new_closed_rows=sorted(candidates),rows=[dict(row=r,function=by[r]['function'],before=by[r]['composed_status'],after='CLOSED',certificate='NFQ_CERTIFICATES.json') for r in sorted(candidates)],no_other_status_change=True,not_a_premise_retirement=True,trust_reclassification='P6/D188 NativeContractSemanticTransport option A; reclassification, not removal',D_counts_after=dict(total=343,CLOSED=21,OPEN=322),whole_ledger_counts_after=dict(total=587,**counts),later_Q_packets='NFN/NFM are cited as boundaries separately; not added to the NFK delta'))
 put('NFQ_AUDIT.json',dict(status='PASS for 16 composed helper certificates; driver OPEN',raw_roots=audited,new_raw_roots=36,reused_raw_roots=6,standard_axioms_only=True,combined_import='NFQ_L048',raw_audit='NFQ_L050',walker_sha256=sha((E/'NFQ_WALKER_SOURCE.lean.txt').read_bytes()),unchanged_NFK_validator_sha256=sha((R/'evidence/ledger6-20261104/NFK_validate.py').read_bytes()),admission='unchanged NFK.certificate_checks/materialize_recipe/row_checks/admit; NFQ adds native/domain/copy/ax2 gates',mutation_tests=tests,exclusions=['K001,L009,L014 prelaunch failures','K012 missing own contract harness declarations','E002 extraction language-item input error','failed Lean elaborations (sorryAx output excluded)','K050/K051 cm31_mul_r wrong prescribed native product certificate form','K058..K060 zero-scan window only; missing generic physical/frame association and one matched pointer control'],retained_trust=['P6/D188 option A','root carrier/ABI/source-to-ELF and compiler/library interpretation','RuntimePersistence','RuntimeReturnData accepted 2026-11-04','RuntimeMemcmp accepted 2026-11-04','sha256 = H runtime realization'],fidelity_controls={'usize':[7,13,14,15],'Option<(u8,usize)>':[5,16,17,18],'CompiledVariant enum':[36,41,42,43],'array4 M31':[38,44,45,46],'Prepared9word record':[32,47,48,49]},no_stub_verified_in_credited_bodies=True))
 print(json.dumps(dict(valid=True,new_functions=16,new_rows=21,remaining_D_rows=322,whole_ledger=counts)))
if __name__=='__main__':build()
