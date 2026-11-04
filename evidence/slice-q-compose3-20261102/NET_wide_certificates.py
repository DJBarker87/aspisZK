from NET_window_certificates import *
W='crates/aspis-core/src/field/wide_exact.rs::WideExact::from_le_bytes'
L='crates/aspis-core/src/field/wide_exact.rs::WideExact::from_limbs'
FIELD='crates/aspis-r1-cost-probe/src/weights.rs::field'
QUERY='crates/aspis-r1-cost-probe/src/candidate.rs::query_values'
WIDE_SRC='5d222d982ce10cf09426f5696b26967eacb826c0256ed67a8a1c44ba20d80ac7'
FIELD_SRC='d89aacc9bc56e78e8d59cbfedb274c5769bb090546fd1e8c76dd700ac205c452'

def audit():
 for start,end,srcname,digest,bad in [(25,32,'crates/aspis-core/src/field/NET_wide_windows.rs',WIDE_SRC,{26,27,29,31}),(32,39,'crates/aspis-r1-cost-probe/src/verifier/NET_fields.rs',FIELD_SRC,{33,34,36,38})]:
  records=[check(f'NET_K{i:03}',int(i in bad)) for i in range(start,end)]
  assert all(r['source_hashes']==records[0]['source_hashes'] for r in records)
  features=obj(E/f'NET_K{start:03}-graph-check.json')['resolved_features_all_crates']
  for i in range(start,end):
   a=f'NET_K{i:03}';assert obj(E/(a+'-graph-check.json'))['resolved_features_all_crates']==features
   env=dict(obj(E/(a+'.json'))['env']);env['RUSTFLAGS']=re.sub(r' --cfg NET_bad_(reply|frame|option)','',env['RUSTFLAGS']);assert env==records[0]['env']
   data=inputs(a);assert hashlib.sha256(data['NET_src/'+srcname].encode()).hexdigest()==digest
  if start==32:
   by={p['name']:p['features'] for p in features}
   assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=set(by['aspis-r1-cost-probe'])
   assert {'r0','pool-v1-kernel'}<=set(by['aspis-statement'])
 assert sha(E/'NET_wide_windows.rs.txt')==WIDE_SRC and sha(E/'NET_fields.rs.txt')==FIELD_SRC
 assert 'called `Option::unwrap()` on a `None` value' in (E/'NET_K035/stdout.log').read_text()
 assert 'encountered no panics' in (E/'NET_K036/stdout.log').read_text()
 return [lean('NET_L017',['NET_WideModel.roundtrip','NET_WideModel.result','NET_WideModel.result_state_effects']),lean('NET_L018',['NET_FieldModel.slot_bound','NET_FieldModel.result','NET_FieldModel.result_state_effects']),lean('NEO_L085',['NEO_FieldView.addresses','NEO_FieldView.result'],False)]

def expected(base):
 proofs=audit();rows=[];edges={};assoc=sha(E/'NET_WIDE_ASSOCIATION.md')
 methods={W:dict(domain='Valid shared byte slice within current57607-byte proof bound; every length and every canonical/noncanonical word',native_pair=['NET_K025','NET_K026'],frame='NET_K027',rejections=['NET_K028','NET_K029'],copy=['NET_K030','NET_K031'],callee=L),FIELD:dict(domain='Current query shared128-byte view and every slot<4; all raw windows including every rejected prefix',native_pair=['NET_K032','NET_K033'],frame='NET_K034',rejections=['NET_K035','NET_K036'],copy=['NET_K037','NET_K038'],callee=W)}
 for row in base['rows']:
  if row['function'] not in methods:continue
  m=methods[row['function']];src=frozen_source(m['native_pair'][0],row['source_file']);a,b=row['frozen_body_byte_range'];assert hashlib.sha256(src[a:b]).hexdigest()==row['frozen_body_sha256']
  externals={}
  for call in row['caller_domain_obligations']:
   if 'callee' in call:continue
   detail=call['call'];syntax=detail.get('expression',detail.get('syntax'))
   assert syntax in (['bytes.len','u32::from_le_bytes'] if row['function']==W else ['E::from_le_bytes(&bytes[i*32..(i+1)*32]).unwrap'])
   externals[call['id']]=dict(syntax=syntax,line=detail['line'],law='Exact byte length/read or actual full Option unwrap; full result and rejection prefix checked')
  rows.append(dict(id='NET-wide-root:'+row['row'],row=row['row'],function=row['function'],domain=m['domain'],parts=['result','state','ordered_effects','native_association','same_live_allocation','lossless_carrier','all_rejection_classes'],lean_evidence=proofs,native_pair=m['native_pair'],frame_control=m['frame'],rejection_pair=m['rejections'],copy_pair=m['copy'],callee=m['callee'],external_obligations=externals,remaining_inner_hypotheses=[],top_hypotheses=['RootPacketDomain','RootPhysicalInterpretation','NativeContractSemanticTransport'],frozen_body_sha256=row['frozen_body_sha256'],association_sha256=assoc))
 for caller,callee in [(W,L),(FIELD,W),(QUERY,FIELD)]:
  parent=next(r for r in base['rows'] if r['function']==caller);edge=caller+' -> '+callee
  if caller==QUERY:
   body=subprocess.check_output(['git','show',base['frozen_revision']+':'+parent['source_file']],cwd=R,text=True)
   for t in ['core::array::from_fn(|s| field(&q[672..800], s))','let q = opening(proof, i);']:assert t in body
  edges[edge]=dict(edge=edge,status='CLOSED',obstacle=None,certificate=dict(id='NET-wide-call:'+edge,caller=caller,callee=callee,source_body_sha256=parent['frozen_body_sha256'],parts=['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association'],lean_evidence=proofs,association_sha256=assoc,residual_inner_hypotheses=[]))
 assert len(rows)==4 and len(edges)==3
 return rows,edges
