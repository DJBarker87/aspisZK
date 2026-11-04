"""Additive NFQ/NFK admission with stricter source/native/model/ax2 checks."""
import pathlib,json,lzma,hashlib,importlib.util,sys,subprocess,re,copy,collections
sys.dont_write_bytecode=True
E=pathlib.Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
J=lambda n:json.loads((E/n).read_text())
sp=importlib.util.spec_from_file_location('NFW_pinned_NFQ',R/'evidence/slice-d-define-20261104/NFQ_certify.py');Q=importlib.util.module_from_spec(sp);sp.loader.exec_module(Q);N=Q.NFK
base=json.loads(lzma.open(R/'evidence/slice-d-define-20261104/NFQ_COMPOSED_LEDGER.json.xz').read());N.BASE_CREDITS=base['NEZ_credits']
by={r['row']:r for r in base['rows']};F='crates/aspis-r1-cost-probe/src/weights.rs::powers'
STANDARD={'propext','Classical.choice','Quot.sound'}
def put(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
def native(i,expected):
 a=f'NFW_K{i:03}';r=J(a+'/receipt.json');ad=J(a+'-admission.json');s=(E/a/'stdout.log').read_text()
 assert r['exit_status']==expected and ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and int(r['swaps'])==0
 assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert J(a+'-graph-check.json')['graph_matches_frozen'] and J(a+'-lock-check.json')['unchanged'] and not J(a+'-source-check.json')['errors']
 assert J(a+'-lock-check.json')['before']==J(a+'-lock-check.json')['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert 'VERIFICATION:- '+('FAILED' if expected else 'SUCCESSFUL') in s
 if expected:assert re.search(r'\*\* 1 of \d+ failed',s) and 'cfg!(NFW_invert)' in s
 src=(E/a/'sources/NFW_src/crates/aspis-r1-cost-probe/src/NFW_weights.rs').read_text()
 assert 'static mut' not in src and not any(t in src for t in ['Atomic','RefCell','UnsafeCell','stub_verified','Option<fn'])
 code='\n'.join(l.split('//',1)[0] for l in src.splitlines())
 assert '.mul(' not in code and 'product(log,*p,x)' in code
 assert 'out[*i]=*p;' in code and '*i+=1;' in code and 'if *i==N {return true;}' in code and 'out:&mut [E;N]' in code
 return r

def build():
 for p,n in [(3,4),(5,6),(7,8)]:
  assert native(p,0)['module']==native(n,1)['module']
 patch=R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch'
 assert sha(patch.read_bytes())=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 # Exact KMX payloads are checked before each native run by the pinned gate.
 gate=(E/'NFW_gate.py').read_text();assert gate==(R/'evidence/slice-d-define-20261104/NFQ_gate.py').read_text().replace('NFQ','NFW')
 audited={}
 assert J('NFW_final_audit/SUMMARY.json')['status']=='PASS'
 for i in range(4):
  r=J(f'NFW_final_audit/proof{i}.json');assert r['exit_status']==0 and int(r['swaps'])==0
  for x in r['results']:
   assert x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<=STANDARD
   audited[x['root']]=x
 assert set(audited)==set(J('NFW_AUDIT_ROOTS.json')) and len(audited)==30
 N.fixtures(J('NFW_final_audit/fixtures.json')['results'])
 assert (E/'NFW_WALKER_SOURCE.lean.txt').read_bytes()==(R/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes()
 # Every theorem module exactly matches a successful focused compilation.
 modules=sorted({r.rsplit('.',1)[0].split('.')[-1] for r in audited})
 for m in modules:
  digest=sha((E/(m+'.lean')).read_bytes())
  assert any(x['exit_status']==0 and x['module']==m and digest in x['source_hashes'].values() for p in E.glob('NFW_L???/receipt.json') for x in [json.loads(p.read_text())]),m
 # Canonical source owner and mathematical model transport are pinned by L016/L019.
 assert 'OWNER FIo_Native.weights.powers := RPz7_FIo_NativeFuns' in (E/'NFW_L016/stdout.log').read_text()
 source=(E/'NFW_PowersCohort.lean').read_text();assert 'XRn_' not in source and 'AspisR1ClaimPreparedBridge.powersPublic' in source
 selected='crates/aspis-core/src/field/wide_exact.rs::WideExact::mul'
 edges=[]
 for c in Q.functions[F]['callees']:
  target=c['function'];active=target==selected
  assert all(by[r]['composed_status']=='CLOSED' for r in c['rows'])
  edges.append(dict(edge=F+' -> '+target,status='CLOSED',certificate=dict(selected=active,callee_packets=c['existing_packets'],domain_proof='NFW_LPi_PowersSource.one_canonical and NFW_LPi_PowersValue.loop derive canonical p at every continuing iteration; gamma is the root canonical input. NFW_LPi_TowerValues.wide_mul returns canonical output and exact natural mulE. K005/K007 record precisely the same operands; K006/K008 fail.' if active else 'Conservative receiver alternative excluded by actual frozen E=WideExact declaration and emitted powers_loop.body, which calls only WideExact.mul. The K005/K007 local-record cut has the identical typed E operands. Lower arithmetic remains inside the CLOSED WideExact callee packet.',lean_root='AspisR1.NFW_PowersCohort.source',native_positive=['NFW_K005','NFW_K007'],matched_control=['NFW_K006','NFW_K008'])))
 physical='Root retained carrier/ABI, compiler/library/Aeneas interpretation, source-to-ELF and P6/D188 option-A native semantic transport; reclassification, no premise removal'
 cc=dict(function=F,rows=['TX1:197','TX2:138'],status='CLOSED',form='ruling(y), one arbitrary-prestate native iteration plus Lean induction',domain='N=7 or N=29; all eight input limbs canonical (<2147483647); no output equality, child-success or native trace assumed at the root',native_positive=['NFW_K005','NFW_K007'],matched_control=['NFW_K006','NFW_K008'],copy_positive='NFW_K003',copy_negative='NFW_K004',kmx_patch_sha256=sha(patch.read_bytes()),lean_root='AspisR1.NFW_PowersCohort.source',native_induction='NFW_LPi_PowersStep/Prefix/Value/Source; NFW_PowersFrame; NFW_LPm_PowersBridge; NFW_NBQ_Powers29',model_association='Canonical RPz7 emitted powers = adopted AspisR1ClaimPreparedBridge.powersPublic on the same ported input/output, via canonical coordinate injectivity; source theorem derives the result',field_stub_table='evidence/slice-d-prepare-20261104/LPh_STUBS.md',frame='Only local out/p/i and local ghost log change. Complete selected-word frame at arbitrary row/limb; input x unchanged. No hash, runtime, observer or writable static.',internal_edges=edges,physical_interpretation=physical,inner_hypotheses_remaining=[])
 certs={};candidates={}
 class Support:
  def support(self,c):
   for x in N.walk(c):
    if isinstance(x,dict) and {'path','sha256'}<=x.keys():assert sha((R/x['path']).read_bytes())==x['sha256']
 support=[p for p in E.glob('NFW_*.lean') if p.stem in modules]+[E/'LPh_STUBS.md',E/'NFW_powers.patch']+[E/f'NFW_K{i:03}'/n for i in range(3,9) for n in ['receipt.json','stdout.log']]
 pins=[dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes())) for p in support]
 for rid in cc['rows']:
  row=by[rid];frozen=subprocess.check_output(['git','show',base['frozen_revision']+':crates/aspis-r1-cost-probe/src/weights.rs'],cwd=R)
  lo,hi=row['frozen_body_byte_range'];body=frozen[lo:hi];assert sha(body)==row['frozen_body_sha256']
  for i in range(3,9):assert body in (E/f'NFW_K{i:03}/sources/NFW_src/crates/aspis-r1-cost-probe/src/weights.rs').read_bytes()
  c=dict(id='NFW::'+rid,row=rid,subject=F,function=F,frozen_body_sha256=row['frozen_body_sha256'],domain=cc['domain'],top_hypotheses=[physical],inner_hypotheses_remaining=[],native=cc,external_obligations={o['id']:dict(classification='source local array store, primitive index/increment and early-return control; complete frame and canonical induction',detail=o['call']) for o in row['caller_domain_obligations'] if 'callee' not in o},support=pins)
  c['semantic_review_sha256']=sha(json.dumps(c,sort_keys=True).encode());N.certificate_checks(Support(),c)
  r=N.materialize_recipe(row,c,'NFW',{'edges':edges})
  for ob in r['caller_domain_obligations']:
   if 'callee' in ob and ob['callee']!=selected:ob['callee_claims']=[]
  assert not N.row_checks(r,row,c)
  certs[rid]=c;candidates[rid]=('NFW',r)
 out=N.admit(base,candidates,certs,{'NFW':cc['rows']});after={r['row']:r for r in out['rows']}
 assert all(after[r]['composed_status']=='CLOSED' for r in candidates)
 assert all(after[r]['composed_status']==by[r]['composed_status'] for r in by if r not in candidates)
 mutation=[];rid=cc['rows'][0];candidate=candidates[rid][1]
 for name,change in [('frozen body',lambda r:r.update(frozen_body_sha256='0'*64)),('open dependency',lambda r:r.update(open_transitive_dependencies=['missing'])),('missing hypothesis',lambda r:r['named_hypotheses'][0].update(discharged_by=None)),('missing selected claim',lambda r:r.update(selected_claims=[]))]:
  bad=copy.deepcopy(candidate);change(bad);assert N.row_checks(bad,by[rid],certs[rid]);mutation.append(name)
 put('NFW_CERTIFICATES.json',certs);put('NFW_EDGES.json',edges);put('NFW_CLOSED.json',dict(new_composed_functions=1,new_composed_rows=2,functions=[cc],driver_root_status='OPEN'))
 raw=json.dumps(out,indent=1).encode();(E/'NFW_COMPOSED_LEDGER.json.xz').write_bytes(lzma.compress(raw));(E/'NFW_COMPOSED_LEDGER.json.sha256').write_text(sha(raw)+'\n')
 put('NFW_LEDGER_DELTA.json',dict(baseline='evidence/slice-d-define-20261104/NFQ_COMPOSED_LEDGER.json.xz',frozen_revision=base['frozen_revision'],new_closed_rows=cc['rows'],new_composed_functions=1,new_composed_rows=2,no_other_status_change=True,D_counts_after=dict(total=343,CLOSED=23,OPEN=320),rows=[dict(row=r,function=F,before=by[r]['composed_status'],after='CLOSED') for r in cc['rows']],trust_reclassification=physical,not_a_premise_retirement=True))
 put('NFW_AUDIT.json',dict(status='PASS for powers; other assigned rows OPEN',raw_roots=audited,standard_axioms_only=True,raw_audit='NFW_L022',combined_import='NFW_L020',walker_sha256=sha((E/'NFW_WALKER_SOURCE.lean.txt').read_bytes()),unchanged_NFK_validator_sha256=sha((R/'evidence/ledger6-20261104/NFK_validate.py').read_bytes()),mutation_tests=mutation,admission='unchanged NFQ/NFK checks reused; stricter native/source/model/copy/ax2 gates added',excluded=['K001 prelaunch own input error','K002 compile-only allocator_api input error','failed Lean elaborations, including every sorryAx output'],cold_release_replay=False))
 print(json.dumps(dict(valid=True,new_composed_functions=1,new_composed_rows=2,remaining_D_rows=320,raw_roots=30)))
if __name__=='__main__':build()
