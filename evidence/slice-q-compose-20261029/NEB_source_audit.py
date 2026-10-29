#!/usr/bin/env python3
"""Pin frozen bodies and resolve statically typed field alternatives.
This is source evidence, never a native proof or a whole-body bridge.
"""
from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent
scope=json.loads((E/'NEB_SCOPE.json').read_text());D=json.loads((R/'evidence/native-ledger3-20261029/NDT_LEDGER.json').read_text())
S=scope['slice'];F='crates/aspis-core/src/field.rs::';W='crates/aspis-core/src/field/wide_exact.rs::'
# Exhaustive direct non-library targets in each listed frozen body. Receiver
# owners come from the declared CM31/QM31/WideExact fields, not name matching.
M={
'CM31::add':['M31::add'],'CM31::double':['CM31::add'],
'CM31::from_le_bytes':['M31::from_le_bytes'],'CM31::inv':['CM31::inv_with','M31::inv'],
'CM31::inv_with':['M31::mul','M31::add','M31::neg','<inverse argument>'],
'CM31::mul':['M31::mul','M31::reduce_u64','M31::sub'],
'CM31::mul_m31':['M31::mul'],'CM31::neg':['M31::neg'],'CM31::new':[],
'CM31::sub':['M31::sub'],'M31::add':[], 'M31::double':['M31::add'],
'M31::from_le_bytes':[], 'M31::inv':['M31::mul','square_n'],
'M31::mul':['reduce_u64'],'M31::reduce_u64':['reduce_u64'],'M31::sub':[],
'QM31::add':['CM31::add'],'QM31::from_le_bytes':['CM31::from_le_bytes'],
'QM31::inv':['QM31::try_inv'],'QM31::is_zero':['CM31::is_zero'],
'QM31::mul':['CM31::mul','CM31::add','CM31::sub','mul_by_r'],
'QM31::mul_m31':['CM31::mul_m31'],'QM31::neg':['CM31::neg'],
'QM31::square':['CM31::square','CM31::mul','CM31::double','CM31::add','mul_by_r'],
'QM31::sub':['CM31::sub'],
'QM31::try_inv':['QM31::is_zero','CM31::square','mul_by_r','CM31::sub','CM31::inv','CM31::mul','CM31::neg'],
'mul_by_r':['M31::double','M31::sub','M31::add'],'reduce_u64':[], 'square_n':['M31::mul']}
WM={'WideExact::add':[F+'QM31::add'],'WideExact::from_le_bytes':[W+'WideExact::from_limbs'],
'WideExact::from_limbs':[],'WideExact::from_qm31':[W+'canonical_qm31'],
'WideExact::mul':[F+'QM31::mul',F+'QM31::add',F+'QM31::sub',W+'mul_u'],
'WideExact::mul_m31':[F+'QM31::mul_m31'],'WideExact::mul_qm31':[W+'canonical_qm31',F+'QM31::mul'],
'WideExact::sub':[F+'QM31::sub'],'WideExact::to_limbs':[], 'canonical_qm31':[], 'mul_u':[F+'mul_by_r']}
actual={F+k:[F+x if not x.startswith('<') else x for x in v] for k,v in M.items()}
actual.update({W+k:v for k,v in WM.items()})
models={F+'CM31::add':['NEB_FieldDomains.cm_arguments','NEB_FieldDomains.cm_add_calls'],F+'CM31::sub':['NEB_FieldDomains.cm_arguments','NEB_FieldDomains.cm_sub_calls'],F+'CM31::mul':['NEB_CMCalls.multiply'],F+'CM31::mul_m31':['NEB_CMCalls.scale'],F+'QM31::add':['NEB_FieldDomains.qm_arguments','NEB_QMCalls.add'],F+'QM31::sub':['NEB_FieldDomains.qm_arguments','NEB_QMCalls.sub'],F+'QM31::mul':['NEB_FieldDomains.qm_arguments','NEB_QMCalls.multiply'],W+'WideExact::mul':['NEB_FieldDomains.wide_arguments','NEB_WideCalls.multiply'],W+'WideExact::mul_qm31':['NEB_FieldDomains.wide_arguments','NEB_WideCalls.mixed'],W+'WideExact::mul_m31':['NEB_WideCalls.scale']}
rows={}
for r in D['rows']:
 if r['function'] in S['functions']:rows.setdefault(r['function'],r)
bodies={}
for f,r in rows.items():
 raw=subprocess.check_output(['git','show',D['frozen_revision']+':'+r['source_file']],cwd=R)
 a,z=r['frozen_body_byte_range'];body=raw[a:z];h=hashlib.sha256(body).hexdigest();assert h==r['frozen_body_sha256']
 bodies[f]=dict(path=r['source_file'],range=[a,z],sha256=h,body=body.decode(),actual_nonlibrary_targets=actual.get(f),resolution_scope='deployed-feature branch only; optional op-count/reference branches excluded by inherited feature pins')
edges=[]
for e in S['internal_edges']:
 caller,callee=e.split(' -> ');known=actual.get(caller)
 r=rows[caller];ob=next(o for o in r['caller_domain_obligations'] if o.get('callee')==callee)
 live=known is None or callee in known
 edges.append(dict(edge=e,caller=caller,callee=callee,obligation_id=ob['id'],status='OPEN',classification='UNRESOLVED_CALL_SITE' if known is None else ('PURE_TYPED_CALL' if live else 'CONSERVATIVE_ALTERNATIVE'),source_body_sha256=bodies[caller]['sha256'],static_resolution='receiver field owners and frozen body' if known is not None else None,selected_target=live if known is not None else None,model_domain_theorems=models.get(caller,[]) if live else [],certificate=None,obstacle=('Native same-execution association, state/effects and inner PhysicalInterpretation discharge not yet certified; model domain is partial evidence only.' if live and models.get(caller) else 'Exact caller-extracted-body domain, native same-input/Result/state/ordered-effect association and inner PhysicalInterpretation discharge missing.' if live else 'Static receiver resolution prepared; reviewed pruning certificate not yet admitted.')))
boundaries=[]
for caller,targets in actual.items():
 if caller not in S['functions']:continue
 for target in targets:
  if target not in S['functions']:
   boundaries.append(dict(caller=caller,callee=target,kind='SLICE_BOUNDARY',action='No out-of-slice bridge work; record and continue independent members',source_body_sha256=bodies[caller]['sha256']))
(E/'NEB_SOURCE_BODIES.json').write_text(json.dumps(dict(frozen_revision=D['frozen_revision'],functions=bodies),indent=1)+'\n')
(E/'NEB_EDGES.json').write_text(json.dumps(dict(schema='NEB-call-domains-v1',slice='Q',edges=edges,boundaries=boundaries),indent=1)+'\n')
print(json.dumps(dict(edges=len(edges),typed_callers=len(actual),boundaries=boundaries,model_domain_edges=sum(bool(e['model_domain_theorems']) for e in edges))))
