import pathlib,json,hashlib,subprocess
E=pathlib.Path('evidence/pv-lib-20261107/lane-SLICE')
j=json.loads((E/'MAP_DELTA.json').read_text())
receipts={r['target']:r for p in E.glob('receipt-*.json') if (r:=json.loads(p.read_text()))['accepted'] and not r['runtime_audit']}
audit=json.loads((E/'RAW_AUDIT.json').read_text()) if (E/'RAW_AUDIT.json').exists() else None
closed={'slice:f32':'PV_LIB_SLICE_F32','slice:f33':'PV_LIB_SLICE_F33'}
for s in j['slots']:
 m=closed.get(s['child'])
 if m and m in receipts:
  r=receipts[m]
  qualification=('Bounded deterministic supplied-machine run graph certified against the literal CLOSED provider clauses. Least certified prefix is not a proved first-source-boundary strengthening. Actual caller Pre/MachineSpec, numbering/suspension and source adequacy remain consumer/composition obligations.' if s['child'].startswith('slice:f') else 'Actual typed f22-derived store projection and complete f7 Drop suffix graph from W2 RuntimeDrop.run, with full replies. Full f7 and its pending f6 source/frame provider remain open; actual caller entry/operand discharge is not claimed.')
  s['status']='INSTANTIATED';s['reason']=qualification
  s['instance']={'module':m,'model':m+'.model','law':m+'.law','theorem':m+'.certified','compiled':True,'attempt':r['attempt'],'source_sha256':r['source_sha256'],'graph_of_function':True,'raw_audited':bool(audit),'qualification':qualification}
  if audit:s['instance']['audit_attempt']=audit['attempt']
  if s['child']=='typedDrop178':s['instance']['provenance']={'branch':'codex/pv-w2-20261108','revision':'fc0340264851248e164a098c170cc53e22857085','sources':['lean/PV_FN_SLICE_f22_TypedDestructor.lean','lean/PV_FN_SLICE_f7_DestructorBinding.lean','lean/PV_FN_SLICE_f7_RuntimeDrop.lean'],'theorems':['PV_FN_SLICE_f22_TypedDestructor.run','PV_FN_SLICE_f22_TypedDestructor.w5_projection_identity','PV_FN_SLICE_f7_DestructorBinding.selected','PV_FN_SLICE_f7_RuntimeDrop.run'],'closed_leaf':'PV_W5_DropLeaf.contract (composed by the provider)'}
 if s['child']=='typedDrop178' and 'PV_LIB_SLICE_TypedDrop' in receipts:
  r=receipts['PV_LIB_SLICE_TypedDrop'];s['support']={'module':r['target'],'theorem':r['target']+'.certified','selector':r['target']+'.selected','attempt':r['attempt'],'source_sha256':r['source_sha256'],'raw_audited':bool(audit),'claim':'Exact typed f22 body graph and actual Regular22 selector by provider names. Full runtime-Drop suffix adapter is not installed.'}
  s['reason']='Typed f22 body graph/selector now compiled. RuntimeDrop needs the remaining W2 replay cone beyond this lane ID block; full runtime/source178 carrier facet remains MISSING-CHILD-LEMMA.'
j['qualification']='Overlay only; shared PLIB_MAP.json untouched. INSTANTIATED counts qualified provider graph adapters, not frozen-contract equivalence, actual caller discharge or parent/root closure.'
j['lane_counts']={status:sum(s['status']==status for s in j['slots']) for status in ['INSTANTIATED','MISSING-CHILD-LEMMA','SPEC-ERROR']}
(E/'MAP_DELTA.json').write_text(json.dumps(j,indent=2)+'\n')
print(j['lane_counts'])
