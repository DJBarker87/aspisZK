"""The complete actual inverse packet; no native-log-only row can pass."""
from NEW_inverse_checks import *
import copy
P='crates/aspis-core/src/field.rs::M31::inv'
MUL='crates/aspis-core/src/field.rs::M31::mul'
SQUARE='crates/aspis-core/src/field.rs::square_n'
def expected(base):
 packet=audit();assert packet==obj(E/'NEW_INVERSE_AUDIT.json')
 prior=obj(E.parent/'slice-q-compose3-20261102/NET_EDGES.json')
 for child in [MUL,SQUARE]:
  outgoing=[edge for edge in prior['edges'] if edge['caller']==child]
  assert outgoing and all(edge['status']=='CLOSED' for edge in outgoing),'unclosed child dependency'
 frozen=subprocess.check_output(['git','show',FROZEN+':crates/aspis-core/src/field.rs'],cwd=R)
 rows=[]
 for row in base['rows']:
  if row['function']!=P:continue
  a,b=row['frozen_body_byte_range'];assert hashlib.sha256(frozen[a:b]).hexdigest()==row['frozen_body_sha256']
  externals={}
  for call in row['caller_domain_obligations']:
   if 'callee' in call:continue
   c=call['call'];assert c['syntax']=='crate::r0_op_count::enter' and c['cfg']==['#[cfg(feature = "r0-op-count")]']
   externals[call['id']]=dict(syntax=c['syntax'],line=c['line'],law='DISABLED_RELEASE_CFG; core feature closure exactly r0 in deployed and native fidelity receipts; no op-count call in actual emitted root')
  rows.append(dict(id='NEW-inverse-root:'+row['row'],row=row['row'],function=P,domain='Every raw U32; zero assertionFailure included',parts=['full_Result','same_input','lossless_U32','all_raw_intermediates','generic_square_loop','ordered_same_result_DAG','model_state_effects','native_fidelity','zero_panic_boundary'],packet=packet,external_obligations=externals,frozen_body_sha256=row['frozen_body_sha256'],remaining_inner_hypotheses=[],top_hypotheses=['RootPacketDomain','RootPhysicalInterpretation','NativeContractSemanticTransport']))
 edges={}
 for e in prior['edges']:
  if e['caller']!=P:continue
  actual=e['callee'] in [MUL,SQUARE]
  certificate=dict(id='NEW-inverse-call:'+e['edge'],caller=P,callee=e['callee'],selected_target=actual,typed_reason=('Actual emitted scalar M31 call at the exact saved DAG operands; child domain all raw values/counts' if actual else 'STATIC_UNREACHABLE; literal extracted type M31 := U32 and complete root body targets scalar M31 only'),parts=['packet_domain','same_arguments','complete_Result','ordered_calls','state_effects','actual_body_association'],lean_evidence=packet['proofs'],native_fidelity=packet['native_pair'],arithmetic_method='Existing emitted Lean arithmetic; never multiplication in Kani',residual_inner_hypotheses=[])
  replacement=copy.deepcopy(e);replacement.update(status='CLOSED',obstacle=None,certificate=certificate)
  edges[e['edge']]=replacement
 assert len(rows)==2 and len(edges)==5
 return rows,edges
