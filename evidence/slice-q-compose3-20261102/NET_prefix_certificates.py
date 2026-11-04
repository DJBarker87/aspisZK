"""Complete current prefix-root recipe. Missing gates cause rejection."""
from NET_window_certificates import *
import NET_prefix_source as source
P='crates/aspis-r1-cost-probe/src/verifier.rs::batch_prefix_products'
MUL='crates/aspis-core/src/field.rs::M31::mul'
ALT=['crates/aspis-core/src/field.rs::CM31::mul','crates/aspis-core/src/field.rs::QM31::mul','crates/aspis-core/src/field/wide_exact.rs::WideExact::mul']

def audit():
 checked=source.check();assert checked==obj(E/'NET_PREFIX_SOURCE.json')
 native=[]
 for i in range(39,85):
  a=f'NET_K{i:03}';r=check(a,int(i%2==0));native.append(r)
  data=inputs(a)
  assert data['NET_src/crates/aspis-r1-cost-probe/src/verifier/NET_prefix.rs']==(E/'NET_prefix.rs.txt').read_text()
  assert r['source_hashes']==native[0]['source_hashes']
  features=obj(E/(a+'-graph-check.json'))['resolved_features_all_crates']
  assert features==obj(E/'NET_K039-graph-check.json')['resolved_features_all_crates']
  env=dict(r['env']);env['RUSTFLAGS']=env['RUSTFLAGS'].replace(' --cfg NET_bad_reply','');assert env==native[0]['env']
  if i<83:assert r['target']==f'verifier::NET_prefix::NET_prefix_{1+(i-39)//2:02}'
  else:assert r['target']=='verifier::NET_prefix::KMX_checks::KMX_ptr_'+('correct' if i==83 else 'wrong')
 for i in [85,86,87,88,101,102]:
  a=f'NET_K{i:03}';r=check(a,int(i%2==0));data=inputs(a)
  assert data['NET_src/crates/aspis-r1-cost-probe/src/verifier/NET_prefix_meta.rs']==(E/'NET_prefix_meta.rs.txt').read_text()
  assert r['source_hashes']==obj(E/'NET_K085/receipt.json')['source_hashes']
 proofs=[lean('NET_L029',['NEI_PrefixProduct.actual','NET_PrefixClosure.capacity_class','NET_PrefixClosure.allocation_invariant','NET_PrefixClosure.step','NET_PrefixClosure.complete','NET_PrefixClosure.observed_result'])]
 return dict(proofs=proofs,native_pairs=[[f'NET_K{39+2*i:03}',f'NET_K{40+2*i:03}'] for i in range(22)],copy_pair=['NET_K083','NET_K084'],constructor_pair=['NET_K085','NET_K086'],empty_pair=['NET_K087','NET_K088'],final_copy_pair=['NET_K101','NET_K102'],association_sha256=sha(E/'NET_PREFIX_ASSOCIATION.md'),source=checked,stub_table_sha256=sha(E/'LPh_STUBS.md'))

def expected(base):
 packet=audit();rows=[];edges={}
 for row in base['rows']:
  if row['function']!=P:continue
  data=frozen_source('NET_K039',row['source_file']);a,b=row['frozen_body_byte_range'];assert hashlib.sha256(data[a:b]).hexdigest()==row['frozen_body_sha256']
  externals={}
  for call in row['caller_domain_obligations']:
   if 'callee' in call:continue
   c=call['call'];syntax=c.get('expression',c.get('syntax'));assert syntax in ['Vec::with_capacity','flat.len','prefixes.push']
   externals[call['id']]=dict(syntax=syntax,line=c['line'],law='Actual empty constructor metadata or actual one-step nongrowing Vec push on arbitrary logical prestate, framed at every live offset')
  rows.append(dict(id='NET-prefix-root:'+row['row'],row=row['row'],function=P,domain='Valid immutable flat M31 slice of length5*n,0<=n<=22; arbitrary raw words and successful standard allocation',parts=['result','state','ordered_effects','native_association','same_live_allocation','lossless_carrier','finite_induction','uninitialized_spare_capacity'],packet=packet,external_obligations=externals,frozen_body_sha256=row['frozen_body_sha256'],remaining_inner_hypotheses=[],top_hypotheses=['RootPacketDomain','RootPhysicalInterpretation','NativeContractSemanticTransport']))
 for callee in [MUL]+ALT:
  edge=P+' -> '+callee
  edges[edge]=dict(edge=edge,status='CLOSED',obstacle=None,certificate=dict(id='NET-prefix-call:'+edge,caller=P,callee=callee,selected_target=(callee==MUL),typed_reason='Frozen flat:&[M31], product=M31::ONE and exact compiled M31 step; alternative carrier methods are unreachable',parts=['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association'],lean_evidence=packet['proofs'],opaque_multiply_theorem='NEG_PrefixStep.multiply (all raw U32 operands)',native_pairs=packet['native_pairs'],association_sha256=packet['association_sha256'],residual_inner_hypotheses=[]))
 assert len(rows)==2 and len(edges)==4
 return rows,edges
