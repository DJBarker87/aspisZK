#!/usr/bin/env python3
"""Additive NFT gates. Reuse NFQ/NFK validators without writing their files."""
import pathlib,json,hashlib,lzma,re,copy,collections,importlib.util,sys,subprocess
sys.dont_write_bytecode=True
E=pathlib.Path(__file__).resolve().parent;R=E.parents[1];Q=E.parent/'slice-d-define-20261104'
sha=lambda b:hashlib.sha256(b).hexdigest()
J=lambda n:json.loads((E/n).read_text())
sp=importlib.util.spec_from_file_location('NFT_prior_NFQ',Q/'NFQ_certify.py');NFQ=importlib.util.module_from_spec(sp);sp.loader.exec_module(NFQ)
NFK=NFQ.NFK
raw=lzma.open(Q/'NFQ_COMPOSED_LEDGER.json.xz').read();assert sha(raw)==(Q/'NFQ_COMPOSED_LEDGER.json.sha256').read_text().strip()
base=json.loads(raw);NFK.BASE_CREDITS=base['NEZ_credits'];by={r['row']:r for r in base['rows']}
functions={f['function']:f for f in json.loads((Q/'NFQ_ORDER.json').read_text())['functions']}
sys.path.insert(0,str(E))
import NFT_review as review
standard={'propext','Classical.choice','Quot.sound'}
F='crates/aspis-core/src/field.rs::';W='crates/aspis-core/src/field/wide_exact.rs::'
specs=[
 (F+'CM31::write_le_bytes',6,7,'NFT_Bytes.cm_value','all raw two-limb inputs; valid uniquely borrowed output slice of length 8',(1,2),(16,17)),
 (F+'QM31::write_le_bytes',8,9,'NFT_Bytes.qm_value','all raw four-limb inputs; valid uniquely borrowed output slice of length 16',(3,4),(18,19)),
 (W+'WideExact::new',12,13,'NFT_WideNew.source','all raw eight-limb input words; full canonical eight-word result',(10,11),None)]

specs += [(f,d['p'],d['n'],d['root'],d['domain'],d['copy'],None)for f,d in review.DETAILS.items()]

def native(k,expected):
 a=f'NFT_K{k:03}';r=J(a+'/receipt.json');ad=J(a+'-admission.json')
 assert r['exit_status']==expected and ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}and int(r['swaps'])==0
 g=J(a+'-graph-check.json');lock=J(a+'-lock-check.json');sc=J(a+'-source-check.json')
 assert g['graph_matches_frozen']and lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'and not sc['errors']
 assert r['env']['CARGO_NET_OFFLINE']=='true'and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert next(p['features']for p in g['selected_closure']if p['name']=='aspis-core')==['r0']
 text=(E/a/'stdout.log').read_text();assert 'VERIFICATION:- '+('FAILED'if expected else 'SUCCESSFUL')in text
 assert 'CBMC timed out'not in text
 if expected:assert re.search(r'\*\* 1 of \d+ failed',text)
 for path,h in r['source_hashes'].items():assert sha((E/a/'sources'/path).read_bytes())==h,(a,path)
 return r,text

def pair(p,n):
 a,_=native(p,0);b,text=native(n,1)
 assert a['module']==b['module']and a['source_hashes']==b['source_hashes']
 assert 'cfg!(NFT_invert)'in text
 assert '--cfg NFT_invert'in b['env']['RUSTFLAGS']and '--cfg NFT_invert'not in a['env']['RUSTFLAGS']
 return a,b

def copy_pair(p,n):
 a,_=native(p,0);b,_=native(n,1)
 assert a['source_hashes']==b['source_hashes']
 assert a['env']==b['env']
 assert a.get('root_package')==b.get('root_package')
 assert a['module'].endswith('positive')and b['module'].endswith('negative')
 return a,b

def audit():
 out={}
 for d,manifest in [('NFT_final_audit','NFT_ROOTS.json'),('NFT_stage2_audit','NFT_STAGE2_ROOTS.json')]:
  assert J(d+'/SUMMARY.json')['status']=='PASS'
  NFK.fixtures(J(d+'/fixtures.json')['results'])
  for file in sorted((E/d).glob('proof*.json')):
   r=json.loads(file.read_text());assert r['exit_status']==0 and int(r['swaps'])==0
   for x in r['results']:
    assert x['equal']and set(x['walked_axioms'])==set(x['collect_axioms'])<=standard
    name='NEP_'+file.stem+'_'+x['root']+'_REACHABLE.txt'
    graph=lzma.open(E/(name+'.xz')).read();assert sha(graph)==(E/(name+'.sha256')).read_text().split()[0]
    x.update(raw_graph=name+'.xz',raw_graph_sha256=sha(graph))
    out[x['root']]=x
  assert set(J(manifest))<=out.keys()
 assert(E/'NFT_WALKER_SOURCE.lean.txt').read_bytes()==(R/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes()
 # Source bytes of every added import must still match a successful pinned compile.
 for line in (E/'NFT_STAGE2_IMPORT.lean').read_text().splitlines():
  if not line.startswith('import NFT_'):continue
  module=line[7:];source=E/(module+'.lean')
  assert source.exists()
  assert any(r['exit_status']==0 and r['module']==module and sha(source.read_bytes())in r['source_hashes'].values() for r in [json.loads(p.read_text())for p in E.glob('NFT_L???/receipt.json')])
 return out
class Support:
 def support(self,c):
  for item in NFK.walk(c):
   if isinstance(item,dict)and{'path','sha256'}<=item.keys():assert sha((R/item['path']).read_bytes())==item['sha256']
def pins(names):return[dict(path=str((E/n).relative_to(R)),sha256=sha((E/n).read_bytes()))for n in names]
def seal(c):c['semantic_review_sha256']=sha(json.dumps(c,sort_keys=True).encode());return c

def build():
 assert review.checks()
 audited=audit();closed=[];edges=[];certs={};candidates={}
 for f,p,n,root,domain,kmx,framepair in specs:
  pair(p,n);assert root in audited
  detail=review.DETAILS.get(f)
  if detail:
   for pair_ids in detail['extra']:pair(*pair_ids)
   for pair_ids in detail.get('copy_extra',[]):copy_pair(*pair_ids)
   assert all(r in audited for r in detail['roots'])
  if framepair:pair(*framepair)
  copy_pair(*kmx)
  assert sha((R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes())=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  module='NFT_QBytes'if root=='NFT_Bytes.qm_value'else root.split('.')[0];source=E/(module+'.lean')
  matching=[json.loads(rr.read_text())for rr in E.glob('NFT_L???/receipt.json')if json.loads(rr.read_text())['exit_status']==0 and json.loads(rr.read_text())['module']==module and sha(source.read_bytes())in json.loads(rr.read_text())['source_hashes'].values()]
  assert matching,root
  child=[]
  for c in functions[f]['callees']:
   target=c['function'];excluded=bool(detail and target in detail['exclude'])or(f==F+'CM31::write_le_bytes'and target==W+'WideExact::to_le_bytes')or(f==F+'QM31::write_le_bytes'and target==f)
   if detail:reason=detail['proof']+(' This inventory union-carrier alternative is statically excluded.'if excluded else ' The exact selected child receives the domain established above.')
   elif excluded:reason='Frozen static receiver resolution: CM31 self.a/self.b are M31; QM31 self.c0/self.c1 are CM31. The union-carrier alternative is not called.'
   elif f==F+'CM31::write_le_bytes':reason='Each same receiver is a raw M31; to_le_bytes admits every u32. Output windows [0,4) and [4,8) are disjoint length4; NFT_Bytes.cm_value proves totality and complete output with no child hypotheses. Native real body executes.'
   elif f==F+'QM31::write_le_bytes':reason='Input output length16 establishes both same [0,8),[8,16) mutable windows have length8, the CLOSED CM writer domain; all raw limb values are allowed. NFT_Bytes.qm_value unfolds and composes the actual checked nested writer, with no child hypotheses. Native real body executes.'
   else:reason='The same two raw QM31 inputs are passed to canonical_qm31, whose domain is all raw words. NFT_WideNew.canonical_source proves exact whole output; reduce_val and reduce_lt prove each modulo value and canonical bound. Native real callee executes.'
   if not excluded:assert target in{z[0]for z in specs}or all(by[r]['composed_status']=='CLOSED'for r in c['rows'])
   edge=dict(edge=f+' -> '+target,status='CLOSED',certificate=dict(native=f'NFT_K{p:03}',lean_root=root,domain_proof=reason,selected=not excluded,callee_packets=c['existing_packets']))
   edges.append(edge);child.append(edge)
  cc=dict(function=f,rows=functions[f]['rows'],status='CLOSED',form='ruling (y) hybrid; real callees, no stub_verified',domain=domain,native_positive=f'NFT_K{p:03}',matched_control=f'NFT_K{n:03}',lean_root=root,model_association='E002 safe reference and NFT_ReferenceEq; constructor actual emitted Post25 definition',axioms=audited[root]['walked_axioms'],internal_edges=child,frame='Complete returned record for constructor; writer unit return and full output slice, plus K016..019 guard-window frame certificates. No caller alias, callback, protocol event or writable static.',KMX=dict(patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',positive=f'NFT_K{kmx[0]:03}',negative=f'NFT_K{kmx[1]:03}'),physical_interpretation='Root-retained same typed carrier/ABI and valid uniquely borrowed buffers, pinned frozen source/deployed features, compiler/library/source-to-ELF and P6/D188 NativeContractSemanticTransport option A; reclassification, no premise retired',inner_hypotheses_remaining=[])
  if detail:
   cc.update(form='ruling (y) hybrid opaque local-record sites; ruling (ad) for fixed data-independent loops; no stub_verified',model_association=detail['proof'],frame='Complete Result and typed output/immutable frame; same-input source cuts and existing model induction as detailed in model_association',paired_model_roots=detail['roots'],native_support_pairs=detail['extra'],copy_support_pairs=detail.get('copy_extra',[]))
  closed.append(cc)
  for rid in cc['rows']:
   r=by[rid];fn=r['function'].split('::')[0];src=subprocess.check_output(['git','show',base['frozen_revision']+':'+fn],cwd=R);a,b=r['frozen_body_byte_range'];body=src[a:b];assert sha(body)==r['frozen_body_sha256']
   for k in[p,n]:assert body in(E/f'NFT_K{k:03}'/'sources/NFT_src'/fn).read_bytes()
   support=[f'NFT_K{k:03}/{x}'for k in[p,n]for x in['receipt.json','stdout.log']]+[module+'.lean','NFT_ROOTS.json','NFT_STAGE2_ROOTS.json','NFT_review.py','NFT_certify.py']
   if detail:
    support+=detail['files']
    support+=[f'NFT_K{k:03}/{x}'for pair_ids in detail['extra']+detail.get('copy_extra',[])+[kmx]for k in pair_ids for x in ['receipt.json','stdout.log']]
   support+=['NFT_stage2_audit/SUMMARY.json','NFT_stage2_audit/BINARY_PIN.json']
   support+=['LPh_STUBS.md','NFT_HARNESSES.patch','NFT_HARNESSES.patch.sha256']
   all_native={p,n,*kmx}
   if framepair:all_native.update(framepair)
   if detail:
    for pair_ids in detail['extra']+detail.get('copy_extra',[]):all_native.update(pair_ids)
   support += [f'NFT_K{k:03}'+suffix for k in sorted(all_native)for suffix in ['-admission.json','-graph-check.json','-lock-check.json','-source-check.json']]
   proof_attempt=matching[-1]['attempt'];support += [proof_attempt+'/receipt.json',proof_attempt+'/stdout.log']
   support=sorted(set(support))
   cert=seal(dict(id='NFT::'+rid,row=rid,subject=f,function=f,frozen_body_sha256=r['frozen_body_sha256'],domain=domain,top_hypotheses=[cc['physical_interpretation']],inner_hypotheses_remaining=[],native=cc,external_obligations={o['id']:dict(classification=detail['proof']if detail else 'safe fixed-range borrow/copy or scalar modulo; exact complete typed body executed and emitted-model equation proved',detail=o['call'])for o in r['caller_domain_obligations']if'callee'not in o},support=pins(support)))
   NFK.certificate_checks(Support(),cert);candidate=NFK.materialize_recipe(r,cert,'NFT',{'edges':edges})
   for ob in candidate['caller_domain_obligations']:
    if'callee'in ob:
     edge=next(e for e in child if e['edge']==f+' -> '+ob['callee'])
     if not edge['certificate']['selected']:ob['callee_claims']=[]
     elif ob['callee']in{z[0]for z in specs}:ob['callee_claims']=['NFT::'+ob['callee']]
   assert not NFK.row_checks(candidate,r,cert);candidates[rid]=('NFT',candidate);certs[rid]=cert
 out=NFK.admit(base,candidates,certs,{'NFT':sorted(candidates)});outby={r['row']:r for r in out['rows']}
 assert all(outby[r]['composed_status']=='CLOSED'for r in candidates)
 assert all(outby[r['row']]['composed_status']==r['composed_status']for r in base['rows']if r['row']not in candidates)
 def put(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
 put('NFT_CLOSED.json',dict(schema_version=1,frozen_revision=base['frozen_revision'],new_composed_functions=len(closed),new_composed_rows=len(candidates),driver_root_status='OPEN',functions=closed));put('NFT_EDGES.json',edges);put('NFT_CERTIFICATES.json',certs)
 put('NFT_LEDGER_DELTA.json',dict(baseline='evidence/slice-d-define-20261104/NFQ_COMPOSED_LEDGER.json.xz',baseline_raw_sha256=sha(raw),new_closed_rows=sorted(candidates),new_functions=len(closed),no_other_status_change=True,D_counts_after=dict(total=343,CLOSED=21+len(candidates),OPEN=322-len(candidates)),whole_ledger_counts_after=dict(collections.Counter(r['composed_status']for r in out['rows'])),trust_reclassification='P6/D188 option A; reclassification, not removal'))
 put('NFT_AUDIT.json',dict(status='PASS',raw_roots=audited,standard_axioms_only=True,raw_audit=['NFT_L021','NFT_L060'],walker_sha256=sha((E/'NFT_WALKER_SOURCE.lean.txt').read_bytes()),prior_NFQ_validator_sha256=sha((Q/'NFQ_certify.py').read_bytes()),unchanged_NFK_validator_sha256=sha((R/'evidence/ledger6-20261104/NFK_validate.py').read_bytes()),retained_trust=['P6/D188 option A','root physical carrier/ABI','compiler/library/Aeneas/source-to-ELF','RuntimePersistence','RuntimeReturnData ACCEPTED','RuntimeMemcmp ACCEPTED','runtime digest = H'],exclusions=['K005 timeout','K069 timeout','K056 pre-CBMC compile failure','E001/L009','L011..016 failed or nonstandard-axiom reference drafts','L022/026..028/033/036..037/041..042/044/048..050/053 rejected drafts']))
 data=json.dumps(out,indent=1).encode();(E/'NFT_COMPOSED_LEDGER.json.xz').write_bytes(lzma.compress(data));(E/'NFT_COMPOSED_LEDGER.json.sha256').write_text(sha(data)+'\n')
 print(json.dumps(dict(valid=True,new_functions=len(closed),new_rows=len(candidates),remaining_D=322-len(candidates))))
if __name__=='__main__':build()
