"""Complete parser root and real caller recipes; inherited checks stay intact."""
from NET_native_review import *
import subprocess,sys,copy
O=E.parent/'slice-q-compose2-20261102'
F='crates/aspis-core/src/field.rs::'
C=F+'CM31::from_le_bytes';Q=F+'QM31::from_le_bytes';M=F+'M31::from_le_bytes'
D='crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots_one'
NATIVE_SOURCE='4f436aa4ad3c69986e5799dd3d05e9b05cdc56e3026dcd95009dcd1760d4452d'
REF='2e0240558aeaf9b15337057bea3b93c190503d71b06dd80102bdf5894aa247f7'

def inputs(a):return json.loads(lzma.decompress((E/(a+'_INPUTS.json.xz')).read_bytes()))

def frozen_source(a,path):
 data=inputs(a);name='NET_src/'+path
 if name in data:return data[name].encode()
 assert path.startswith(('crates/','programs/'))
 raw=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],cwd=R)
 pins=json.loads(data['NET_SOURCE_PINS.json'])
 assert pins[path]==hashlib.sha256(raw).hexdigest(),'missing frozen dependency differs from Git'
 assert not obj(E/(a+'-source-check.json'))['errors']
 return raw

def lean(a,names,own=True):
 p=(E if own else O)/a/'receipt.json';r=obj(p)
 assert r['exit_status']==0 and r['limits']==CAPS and int(r['swaps'])==0
 for n in names:
  lines=[s for s in r['print_axioms'] if s.startswith("'"+n+"'")];assert len(lines)==1
  line=lines[0]
  if 'does not depend on any axioms' not in line:
   axioms=re.search(r'axioms: \[([^]]*)\]',line);assert axioms
   assert {x.strip() for x in axioms[1].split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'}
 for f,h in r['source_hashes'].items():assert sha((E if own else O)/a/'sources'/f)==h
 return dict(receipt=str(p.relative_to(R)),sha256=sha(p),theorems=names)

def audit():
 records=[check(f'NET_K{i:03}',int(i in [18,20,21,23,24])) for i in range(17,25)]
 assert all(r['source_hashes']==records[0]['source_hashes'] for r in records)
 features=obj(E/'NET_K017-graph-check.json')['resolved_features_all_crates']
 for i in range(17,25):
  a=f'NET_K{i:03}';assert obj(E/(a+'-graph-check.json'))['resolved_features_all_crates']==features
  env=dict(obj(E/(a+'.json'))['env']);env['RUSTFLAGS']=re.sub(r' --cfg NET_bad_(reply|frame)','',env['RUSTFLAGS'])
  assert env==records[0]['env']
  data=inputs(a);assert hashlib.sha256(data['NET_src/crates/aspis-core/src/field/NET_windows.rs'].encode()).hexdigest()==NATIVE_SOURCE
  assert hashlib.sha256(data['NET_src/crates/aspis-core/src/field/NET_window_reference.rs'].encode()).hexdigest()==REF
 assert sha(E/'NET_windows.rs.txt')==NATIVE_SOURCE and sha(E/'NET_window_reference.rs')==REF
 assert sha(O/'NEO_window_reference.rs')==REF
 pins=obj(O/'NEO_WINDOW2_EXTRACTION_PINS.json');assert pins['exit']==0 and pins['rust_reference_sha256']==REF
 for f,h in pins['outputs'].items():assert sha(O/f)==h
 assert obj(O/'NEO_E009/receipt.json')['exit_status']==0
 proofs=[lean('NET_L015',['NET_ParserComposed.c_roundtrip','NET_ParserComposed.q_roundtrip','NET_ParserComposed.complex_result_state_effects','NET_ParserComposed.quadratic_result_state_effects']),lean('NET_L012',['NET_CallerWindows.quadratic','NET_CallerWindows.complex']),lean('NET_L016',['NET_WindowEmbedding.native_window']),lean('NEO_L072',['NEO_QModelBinding.complex','NEO_QModelBinding.quadratic'],False)]
 return dict(proofs=proofs,copy_pair=['NET_K017','NET_K018'],same_allocation_bytes=608,native_source_sha256=NATIVE_SOURCE,reference_sha256=REF,association_sha256=sha(E/'NET_WINDOW_ASSOCIATION.md'))

def expected(base):
 native=audit();rows=[];edges={}
 methods={C:('complex',8,['NET_K019','NET_K020','NET_K021']),Q:('quadratic',16,['NET_K022','NET_K023','NET_K024'])}
 for row in base['rows']:
  if row['function'] not in methods:continue
  method,width,pair=methods[row['function']];raw=inputs(pair[0])['NET_src/'+row['source_file']].encode();a,b=row['frozen_body_byte_range'];assert hashlib.sha256(raw[a:b]).hexdigest()==row['frozen_body_sha256']
  externals={}
  for call in row['caller_domain_obligations']:
   if 'callee' in call:continue
   detail=call['call'];syntax=detail.get('expression',detail.get('syntax'))
   assert syntax in (['bytes[0..4].try_into','bytes[4..8].try_into','Some'] if method=='complex' else ['Some'])
   externals[call['id']]=dict(syntax=syntax,line=detail['line'],law='Exact fixed-width standard conversion / owned typed constructor; both Result branches preserved')
  rows.append(dict(id='NET-window-root:'+row['row'],row=row['row'],function=row['function'],domain=f'Valid immutable borrowed view of exactly {width} arbitrary bytes, at the checked current call windows; no success/canonicality condition',parts=['result','state','ordered_effects','native_association','same_live_allocation','lossless_carrier'],lean_evidence=native['proofs'],native_pair=pair[:2],frame_control=pair[2],copy_pair=native['copy_pair'],frozen_body_sha256=row['frozen_body_sha256'],external_obligations=externals,callee=M if method=='complex' else C,remaining_inner_hypotheses=[],top_hypotheses=['RootPacketDomain','RootPhysicalInterpretation','NativeContractSemanticTransport'],association_sha256=native['association_sha256']))
 for caller,callee in [(C,M),(Q,C),(D,Q)]:
  edge=caller+' -> '+callee;parent=next(r for r in base['rows'] if r['function']==caller)
  if caller==D:
   body=subprocess.check_output(['git','show',base['frozen_revision']+':'+parent['source_file']],cwd=R,text=True)
   for t in ['q: &[u8; 608]','slot*120+104..slot*120+120','480 + slot * 32 + 0 * 16','480 + slot * 32 + 1 * 16','QM31::from_le_bytes(&q[offset0..offset0 + 16])','QM31::from_le_bytes(&q[offset1..offset1 + 16])']:assert t in body
  edges[edge]=dict(edge=edge,status='CLOSED',obstacle=None,certificate=dict(id='NET-parser-call:'+edge,caller=caller,callee=callee,source_body_sha256=parent['frozen_body_sha256'],parts=['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association'],lean_evidence=native['proofs'],native_pair=(methods[C][2][:2] if caller==C else methods[Q][2][:2]),copy_pair=native['copy_pair'],same_allocation_bytes=608,residual_inner_hypotheses=[],association_sha256=native['association_sha256']))
 assert len(rows)==4 and len(edges)==3
 return rows,edges
