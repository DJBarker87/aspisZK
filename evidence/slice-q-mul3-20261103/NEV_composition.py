"""Narrow prefix extension of the unchanged-check NEI/NDT composition gate."""
from pathlib import Path
import json,hashlib,copy,sys,types,inspect,subprocess,re
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
from NEV_import_nei import load
import NEV_prefix_validate as gate
obj=lambda p:json.loads(Path(p).read_text());sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
PREFIX='crates/aspis-r1-cost-probe/src/verifier.rs::batch_prefix_products'
MUL='crates/aspis-core/src/field.rs::M31::mul'
F=gate.F
DOMAIN='flat.val.length=5*k for k<=22; every raw U32 input. Prefix allocation/length/capacity is derived internally from the actual constructor and loop steps, never a root input premise.'

def legacy_pairs():
 I=E.parent/'slice-q-mul2-20261101'
 for a,b,flag in [('NEI_K007','NEI_K008','NEI_wrong_read')]:
  p=obj(I/a/'receipt.json');n=obj(I/b/'receipt.json')
  assert p['exit_status']==0 and n['exit_status']==1 and p['source_hashes']==n['source_hashes']
  pe=dict(p['env']);ne=dict(n['env']);assert ne.pop('RUSTFLAGS')==pe.pop('RUSTFLAGS')+' --cfg '+flag and pe==ne
  assert p['native_command']==n['native_command']
  for name,d in [(a,p),(b,n)]:
   assert d['swaps']=='0' and d['limits']==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],['6442450944','8589934592','0','64']))
   assert obj(I/(name+'-graph-check.json'))['graph_matches_frozen']
   assert obj(I/(name+'-lock-check.json'))['unchanged']
   assert obj(I/(name+'-rule16-check.json'))['static_declarations']==[]
   for path,h in d['source_hashes'].items():assert sha(I/name/'sources'/path)==h
  assert 'VERIFICATION:- SUCCESSFUL' in (I/a/'stdout.log').read_text()
  text=(I/b/'stdout.log').read_text();assert 'VERIFICATION:- FAILED' in text and 'timed out' not in text

def own_native(a,exit,target):
 d=obj(E/a/'receipt.json');assert d['exit_status']==exit and d['module']==target and d['kind']=='kani'
 assert d['swaps']=='0' and d['limits']==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],['6442450944','8589934592','0','64']))
 assert d['env']['CARGO_NET_OFFLINE']=='true' and '--harness-timeout' in d['native_command'] and d['native_command'][d['native_command'].index('--harness-timeout')+1]=='90s'
 for name,h in d['source_hashes'].items():assert sha(E/a/'sources'/name)==h
 assert obj(E/(a+'-graph-check.json'))['graph_matches_frozen'] and obj(E/(a+'-graph-check.json'))['resolved_features_all_crates']
 lock=obj(E/(a+'-lock-check.json'));assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert obj(E/(a+'-rule16-check.json'))['static_declarations']==[] and obj(E/(a+'-frozen-source-check.json'))['passed']
 ad=obj(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
 log=(E/a/'stdout.log').read_text();assert 'timed out' not in log and 'CBMC failed' not in log
 assert ('VERIFICATION:- SUCCESSFUL' if exit==0 else 'VERIFICATION:- FAILED') in log
 if exit:assert re.search(r'\*\* 1 of \d+ failed',log) and 'core::panicking::assert_failed_inner' in log
 return d

def packet():
 native=gate.audit();legacy_pairs()
 extra=dict(receipt=str((E/'NEV_L009/receipt.json').relative_to(R)),receipt_sha256=sha(E/'NEV_L009/receipt.json'),theorems=['NEV_PrefixPacket.result_state_effects'])
 cproof=gate.neb.check_receipt(extra,extra['theorems'][0]);native['lean_evidence'].append(extra)
 # Exact actual extraction; opaque M31 arithmetic is associated by the complete
 # NEI actual field forest and the imported same-operand product theorem.
 G=E.parent/'slice-q-mul-20261029';pins=obj(G/'NEG_E018/NEG_EXTRACTION_PINS.json')
 assert pins['exit']==pins['charon_exit']==0 and pins['lock_before']==pins['lock_after']
 for name,h in pins['outputs'].items():
  p=G/name
  if not p.exists() and name.endswith('_Template.lean'):p=G/(name+'.txt')
  assert sha(p)==h
 source=obj(E/'NEV_FROZEN.json')['crates/aspis-r1-cost-probe/src/verifier.rs']
 from NEI_validate import function
 body=function(source,'batch_prefix_products');h=hashlib.sha256(body[body.index('{'):].encode()).hexdigest()
 emitted=(G/'NEG_PrefixFull/Funs.lean').read_text()
 assert 'let product1 ← aspis_core.field.M31.mul product value' in emitted
 assert all('aspis_core.field.'+t+'.mul' not in emitted for t in ['CM31','QM31','wide_exact.WideExact'])
 assert 'flat:&[M31]' in body and 'let mut product=M31::ONE' in body
 assert '.inv(' not in body and body.count('prefixes.push(product)')==1
 library=obj(E/'NEV_NATIVE_LIBRARY_PINS.json');assert '53732d5e0' in library['rustc_version'] and library['objects']
 std=(E/'NEV_RUST_VEC.rs.txt').read_text()
 for text in ['pub fn push(&mut self, value: T)','let _ = self.push_mut(value);','if len == self.buf.capacity()','let end = self.as_mut_ptr().add(len);','ptr::write(end, value);','self.len = len + 1;']:assert text in std
 require_source=obj(E/'NEV_RUST_VEC_SOURCE.json');assert sha(E/'NEV_RUST_VEC.rs.txt')==require_source['sha256']
 for a,exit,target in [('NEV_K026',0,'NEV_copy::KMX_checks::KMX_ptr_correct'),('NEV_K027',1,'NEV_copy::KMX_checks::KMX_ptr_wrong')]:
  d=own_native(a,exit,target)
  assert obj(E/(a+'-graph-check.json'))['graph_matches_frozen'] and obj(E/(a+'-lock-check.json'))['unchanged']
  assert d['source_hashes']==obj(E/'NEV_K026/receipt.json')['source_hashes']
 for a,exit in [('NEV_K028',0),('NEV_K029',1)]:
  d=own_native(a,exit,'verifier::NEV_prefix_step::allocation_capacity')
  assert obj(E/(a+'-graph-check.json'))['graph_matches_frozen'] and obj(E/(a+'-lock-check.json'))['unchanged']
  assert d['source_hashes']==obj(E/'NEV_K028/receipt.json')['source_hashes']
 native.update(status='CLOSED_CONDITIONAL_PREFIX_LOCAL',library_footprint=dict(source_context_sha256=sha(E/'NEV_RUST_VEC_SOURCE.json'),native_library_pins_sha256=sha(E/'NEV_NATIVE_LIBRARY_PINS.json'),law='With live length<capacity, actual push_mut skips growth, writes at ptr+length, then increments length; no read from uninitialised spare. Compiler/library correspondence remains P7/P6, no Vec::push specification assumed'),allocation_pair=['NEV_K028','NEV_K029'],read_product_pair=['NEI_K007','NEI_K008'],copy_pair=['NEV_K026','NEV_K027'],remaining=['incoming for_range gather/borrow/append same-native-call association; parent inverse/nonzero/collect obligations stay OPEN'])
 (E/'NEV_PREFIX_NATIVE_REVIEW.json').write_text(json.dumps(native,indent=2)+'\n')
 return dict(claim_id='NEV::prefix',function=PREFIX,status='CLOSED-CONDITIONAL',route='D188_ACTUAL_BODY_NATIVE_APPEND_FAMILY',frozen_revision=F,source_body_sha256=h,domain=DOMAIN,lean_evidence=native['lean_evidence'],review=dict(path=str((E/'NEV_PREFIX_ASSOCIATION.md').relative_to(R)),sha256=sha(E/'NEV_PREFIX_ASSOCIATION.md')),native_review=dict(path=str((E/'NEV_PREFIX_NATIVE_REVIEW.json').relative_to(R)),sha256=sha(E/'NEV_PREFIX_NATIVE_REVIEW.json')),remaining_inner_hypotheses=[],trust_reclassification='P6/D188 option A retained; reclassification, never removal',new_native_pairs=native['pairs'],reused_native_pairs=[['NEI_K007','NEI_K008']],allocation_pair=['NEV_K028','NEV_K029'],copy_pair=['NEV_K026','NEV_K027'],suspended_neb_credits_restored=[])

def context():
 c=load();p=packet();old_apply=c.apply;old_expected=c.expected;old_resolution=c.leaves.resolutions
 # Preserve every inherited gate, adding only a narrowly checked standard-call
 # classification for the four exact prefix source occurrences.
 original=c.added
 marker="     else:require(False,'unregistered external obligation kind')"
 branch="     elif ext['kind']=='NEV_PREFIX_STD':\n      _NEV_check_prefix_external(row,o,ext,rc)\n      o.update(status='CLOSED',discharged_by=rc['id']+':exact-prefix-std-occurrence')\n"
 assert original.count(marker)==1
 source=original.replace(marker,branch+marker);assert source.replace(branch,'')==original
 path=E/'NEV_PREFIX_NEB_ADDITIVE.py';path.write_text(source)
 n=types.ModuleType('NEV_PREFIX_NEB_ADDITIVE');n.__file__=str(path)
 exec(compile(source,str(path),'exec'),n.__dict__)
 n.E=c.B;n.R=R;n.N=E.parent/'native-ledger3-20261029'
 for name,value in c.neb.__dict__.items():
  if name.startswith('_NEI_'):setattr(n,name,value)
 def external(row,o,ext,rc):
  assert row['function']==PREFIX and row['frozen_body_sha256']==p['source_body_sha256']
  call=o['call'];syntax=call.get('expression',call.get('syntax'))
  assert (syntax,call['line']) in [('Vec::with_capacity',135),('flat.len',135),('flat.len',138),('prefixes.push',140)]
  assert ext==dict(kind='NEV_PREFIX_STD',syntax=syntax,line=call['line'],source_body_sha256=row['frozen_body_sha256'],native_review=p['native_review'])
  assert rc['function']==PREFIX and rc['lean_evidence']==p['lean_evidence']
 n._NEV_check_prefix_external=external;c.neb=n
 def apply(base):
  out,changes=old_apply(base)
  for row in out['rows']:
   if row['function']!=PREFIX:continue
   assert row['frozen_body_verified'] and row['frozen_body_sha256']==p['source_body_sha256']
   row.update(bridge_status='CLOSED-CONDITIONAL',selected_claims=[p['claim_id']],no_credit_reason=None)
   if p['claim_id'] not in row['claim_ids']:row['claim_ids'].append(p['claim_id'])
   for domain in row['inventory_domain_obligations']:
    assert (row['row'],domain['unit']) in [('TX1:185','geometry'),('TX2:111','U08')],'unexpected prefix inventory unit'
    domain['NEV_original_parent_assignment']=domain['domain']
    domain['domain']='Prefix fragment input domain: '+DOMAIN
    domain['NEV_scope_correction']='This leaf returns prefixes/product only and emits no inverse vector. The original complete geometry inverse/nonzero/collect obligations remain on QueryGeometry::for_range, which stays OPEN.'
   row['named_hypotheses']=[dict(name=p['claim_id']+'.PacketDomain',statement=DOMAIN,discharged_by=None),dict(name=p['claim_id']+'.PhysicalInterpretation',statement='Frozen source/ABI, valid disjoint buffers, admitted allocator/Std and P6/D188 semantic transport; spare-capacity no-read footprint reviewed',discharged_by=None)]
   row['reviewed_packet_updates'].append(dict(prefix='NEV',disposition='New same-prestate append family; no old suspended native credit; geometry inverse output clauses belong to parent and are not claimed by this prefix fragment',evidence=[str((E/'NEV_PREFIX_PACKET.json').relative_to(R))]))
  for row in out['rows']:
   for o in row['caller_domain_obligations']:
    if o.get('callee')==PREFIX:o.update(callee_claims=[p['claim_id']],callee_local_status='CLOSED-CONDITIONAL',required_named_hypotheses=[p['claim_id']+'.PacketDomain',p['claim_id']+'.PhysicalInterpretation'])
  return out,changes
 def resolution(edge):
  e=old_resolution(edge)
  if e['caller']!=PREFIX:return e
  assert e['source_body_sha256']==p['source_body_sha256']
  assert e['callee'] in [MUL,'crates/aspis-core/src/field.rs::CM31::mul','crates/aspis-core/src/field.rs::QM31::mul','crates/aspis-core/src/field/wide_exact.rs::WideExact::mul']
  e=copy.deepcopy(e);e.update(selected_target=e['callee']==MUL,classification='PURE_TYPED_CALL' if e['callee']==MUL else 'CONSERVATIVE_ALTERNATIVE',static_resolution='Frozen M31 arguments/product; exact NEG E018 M31-only emitted site; NEI native M31 read/product log; NEV_PrefixCalls.m31_site')
  return e
 def recipes(base):
  roots={};edges={};proofs=p['lean_evidence'];names=[t for item in proofs for t in item['theorems']]
  review=dict(**p['review'],conclusion_hiding=False,statement_and_native_association_checked=True)
  for row in base['rows']:
   if row['function']!=PREFIX:continue
   externals={}
   for o in row['caller_domain_obligations']:
    if 'call' not in o:continue
    call=o['call'];syntax=call.get('expression',call.get('syntax'))
    externals[o['id']]=dict(kind='NEV_PREFIX_STD',syntax=syntax,line=call['line'],source_body_sha256=row['frozen_body_sha256'],native_review=p['native_review'])
   roots[row['row']]=dict(id='NEV-prefix-root:'+row['row'],row=row['row'],function=PREFIX,frozen_body_sha256=row['frozen_body_sha256'],selected_claims=row['selected_claims'],named_hypotheses_discharged=[h['name'] for h in row['named_hypotheses']],inventory_domains_discharged=[o['unit'] for o in row['inventory_domain_obligations']],parts=['result','state','ordered_effects','native_association'],lean_evidence=proofs,remaining_inner_hypotheses=[],top_hypotheses=[PREFIX+'.PacketDomain',PREFIX+'.PhysicalInterpretation','CompositionTrustOptionA'],review=review,native_review=p['native_review'],external_obligations=externals)
  for edge in obj(c.B/'NEB_EDGES.json')['edges']:
   if edge['caller']!=PREFIX:continue
   edge=resolution(edge);children=[r for r in base['rows'] if r['function']==edge['callee']];inner=sorted(set(h['name'] for r in children for h in r['named_hypotheses']))
   edges[edge['edge']]=dict(id='NEV-prefix-edge:'+edge['obligation_id'],edge=edge['edge'],status='CLOSED',kind='DIRECT_CALL' if edge['selected_target'] else 'STATIC_UNREACHABLE',frozen_revision=F,source_body_sha256=p['source_body_sha256'],selected_callee_claims=sorted(set(claim for r in children for claim in r['selected_claims'])),inner_hypotheses_discharged=inner,hypothesis_discharge_theorems={h:names for h in inner},parts={part:dict(theorems=names) for part in ['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association']},lean_evidence=proofs,theorems=names,residual_hypotheses=[],review=review,native_review=p['native_review'],trust=p['trust_reclassification'])
  return edges,roots
 def expected(base):
  old_edges,old_rows=old_expected(base);new_edges,new_rows=recipes(base)
  assert not set(old_edges)&set(new_edges) and not set(old_rows)&set(new_rows)
  return {**old_edges,**new_edges},{**old_rows,**new_rows}
 c.leaves.apply=apply;c.leaves.resolutions=resolution;c.certificates.expected=expected
 def prepare(base):
  refreshed,_=apply(base);edges=c.prepare(base);approved,roots=recipes(refreshed)
  for i,e in enumerate(edges['edges']):
   e=resolution(e);edges['edges'][i]=e
   if e['edge'] in approved:e.update(certificate=approved[e['edge']],status='CLOSED',obstacle=None)
   e['required_named_hypotheses']=sorted(set(h['name'] for r in refreshed['rows'] if r['function']==e['callee'] for h in r['named_hypotheses']))
  edges['row_certificates']+=list(roots.values())
  return edges
 def validate(base,edges):
  refreshed,_=apply(base);approved,roots=recipes(refreshed)
  for cert in edges.get('row_certificates',[]):
   if cert['id'].startswith('NEV-'):assert cert==roots[cert['row']],'unregistered prefix root'
   else:
    assert cert['id'].startswith('NEI-'),'older native root credit supplied'
    assert all(x['receipt'].startswith(str(c.E.relative_to(R))+'/') for x in cert['lean_evidence']),'older proof/native recipe supplied'
  for edge in edges['edges']:
   if edge.get('certificate'):
    cert=edge['certificate']
    if cert['id'].startswith('NEV-'):assert cert==approved[edge['edge']],'unregistered prefix edge'
    else:assert cert['id'].startswith('NEI-'),'older native edge credit supplied'
    if cert['kind']=='STATIC_UNREACHABLE':assert edge['classification']=='CONSERVATIVE_ALTERNATIVE' and edge['selected_target'] is False,'static target resolution contradicted'
    else:assert edge['selected_target'] is not False,'direct target resolution contradicted'
  return n.extend(base,edges)
 (E/'NEV_PREFIX_PACKET.json').write_text(json.dumps(p,indent=2)+'\n')
 return c,p,prepare,validate
if __name__=='__main__':
 c,p,prepare,validate=context();base=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json')
 edges=prepare(base);out,delta=validate(base,edges)
 (E/'NEV_EDGES.json').write_text(json.dumps(edges,separators=(',',':'))+'\n')
 (E/'NEV_DERIVED_LEDGER.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
 (E/'NEV_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=2)+'\n')
 old=set(obj(E/'NEV_NEI_REPLAY_DELTA.json')['composed_rows_closed']);new=set(delta['composed_rows_closed'])-old
 (E/'NEV_CLOSED.json').write_text(json.dumps(dict(schema='NEV-closed-v1',newly_closed=sorted(new),all_component_closed=delta['composed_rows_closed'],edge_closed=delta['edge_closed'],roots=delta['roots'],trust='P6/D188 retained; reclassification, never removal'),indent=2)+'\n')
 print(json.dumps(dict(new=sorted(new),all=len(delta['composed_rows_closed']),edges=delta['edge_closed'])))
