"""Slice-Q geometry root packet: never promote component-only evidence."""
from pathlib import Path
import sys,json,copy,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent
O=E.parent/'slice-q-compose4-20261104'
sys.path.insert(0,str(O))
from NFB_root_source import ROOT,REV
from NFB_proof_checks import accepted
from NFB_geometry_gates import check as native
from NFB_root_source import check as source
from NFB_std_collect_checks import check as std
from NFB_caller_checks import check as callers
from NFB_external_checks import check as externals
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
PROOFS=['NFB_ZeroScan','NFB_ZeroFinite','NFB_PhysicalFrame','NFB_PrivateFrame','NFB_GatherFrame','NFB_MulDischarge',
'NFB_ResizeTrace','NFB_RowRef.Types','NFB_RowRef.FunsExternal','NFB_RowRef.Funs','NFB_RowPrimitives','NFB_RowIndex',
'NFB_RowLog','NFB_RowG','NFB_QueryIterator','NFB_GeometryInstall','NFB_GatherTrace','NFB_GatherChain','NFB_RangeTrace',
'NFB_ActualStep','NFB_RootGather','NFB_TerminalCuts','NFB_ReverseTrace','NFB_ReverseAssociation',
'NFB_CollectorTrace','NFB_CollectAssociation','NFB_TraceBounds','NFB_AcceptedGather','NFB_TerminalFrame',
'NFB_PrefixDomain','NFB_ReturnedBuffers','NFB_ResizeAssociation','NFB_BackwardCongr','NFB_BackwardTransport',
'NFB_TerminalAssociation','NFB_GeometryComposed']
ACTUAL={'crates/aspis-core/src/field.rs::M31::'+s for s in ['double','sub','mul','inv']}|{
'crates/aspis-core/src/r0/domain.rs::FibreIndex::new',
'crates/aspis-r1-cost-probe/src/fast_domain.rs::fibre_point',
'crates/aspis-r1-cost-probe/src/fast_domain.rs::line_node',
'crates/aspis-r1-cost-probe/src/verifier.rs::batch_prefix_products'}
def packet():
 p=dict(proofs=[accepted(m) for m in PROOFS],native=native(),source=source(),standard=std(),callers=callers(),
  multiplication_stub_table_sha256=sha(E/'NFB_LPh_STUBS.md'),installed_std_libraries=obj(E/'NFB_STD_LIBRARY_PINS.json'),
  native_patch_sha256=sha(E/'NFB_NATIVE.patch'),root_math='NFB_GeometryComposed.result_state_effects',
  physical_association='NFB_GeometryComposed.accepted_physical; NFB_RangeTrace.complete includes every partial Result',
  remaining_inner_hypotheses=[],own_domain='Valid original &[u32;22], deployed (0,10)/(10,22), valid shared child/table memory; standard successful allocations or approved abort interpretation',
  top_hypotheses=['RootPacketDomain','RootPhysicalInterpretation','NativeContractSemanticTransport','Allocator'],
  trust='P6/D188 option A reclassification, never removal; no empty native panic-I/O or source-to-ELF proof claim')
 assert p['remaining_inner_hypotheses']==[]
 return p

def expected(base):
 p=packet();assert p==obj(E/'NFB_GEOMETRY_PACKET.json'),'packet source/evidence drift'
 old=obj(O/'NEW_EDGES.json')
 # Real callees only; statically impossible inventory alternatives are not deps.
 for child in ACTUAL:
  outgoing=[e for e in old['edges'] if e['caller']==child]
  assert all(e['status']=='CLOSED' for e in outgoing),(child,'open real child')
 rows=[]
 frozen=subprocess.check_output(['git','show',REV+':'+ROOT.split('::')[0]],cwd=R)
 for row in base['rows']:
  if row['function']!=ROOT:continue
  a,b=row['frozen_body_byte_range'];assert hashlib.sha256(frozen[a:b]).hexdigest()==row['frozen_body_sha256']
  assert row['frozen_body_sha256']=='cecda71c277c78a80c9dedd96c0148a2907410736135eeef24f3c1c0ffeaf154'
  external_laws,inventory_laws=externals(row)
  rows.append(dict(external_obligations=external_laws,inventory_obligations=inventory_laws,id='NFB-geometry-root:'+row['row'],row=row['row'],function=ROOT,
   domain=p['own_domain'],parts=['full_Result','persistent_state','semantic_effects','native_callsite_association','same_buffer_frames','finite_trace','child_domains','returned_ownership'],
   packet_sha256=sha(E/'NFB_GEOMETRY_PACKET.json'),frozen_body_sha256=row['frozen_body_sha256'],
   remaining_inner_hypotheses=[],top_hypotheses=p['top_hypotheses']))
 assert {r['row'] for r in rows}=={'TX1:181','TX2:104'}
 edges={}
 for e in old['edges']:
  if e['caller']!=ROOT:continue
  actual=e['callee'] in ACTUAL
  n=copy.deepcopy(e)
  n.update(status='CLOSED',obstacle=None,classification='COMPOSED_CALL_SITE' if actual else 'STATIC_UNREACHABLE',selected_target=actual,
   model_domain_theorems=['NFB_RowG.complete','NFB_MulDischarge.multiplication','NFB_GeometryComposed.accepted_physical'],
   certificate=dict(id='NFB-geometry-call:'+e['edge'],caller=ROOT,callee=e['callee'],selected_target=actual,
    typed_reason=('Same saved argument/result/private owner in the composed root packet' if actual else 'Frozen typed M31 receivers, native M31 G/log/windows and extracted M31/U32 association exclude this alternative'),
    packet_sha256=sha(E/'NFB_GEOMETRY_PACKET.json'),parts=['packet_domain','same_arguments_Result','ordered_calls','state_effects','physical_interpretation','native_association'],residual_inner_hypotheses=[]))
  edges[e['edge']]=n
 assert len(edges)==17
 return rows,edges
