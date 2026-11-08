"""Overlay the exact sixty session-5 assignments, without editing the map."""
import collections,hashlib,json,pathlib,re,subprocess
E=pathlib.Path('evidence/pv-lib-20261107/lane-B')
BASE='5e397cb3878';MERGE='fbc60bd811d36ca79d71aabc563f709c26b9d2da'
old=json.loads(subprocess.check_output(['git','show',BASE+':evidence/pv-lib-20261107/PLIB_MAP.json']))
merged=json.loads(subprocess.check_output(['git','show',MERGE+':evidence/pv-lib-20261107/PLIB_MAP.json']))
current={s['slot']:s for s in merged['slots']}
corrections={s['slot']:s for s in json.loads((E/'SPEC-CORRECTIONS-S5.json').read_text())['slots']}
pairs=[(170,277),(170,278),(170,279),(170,280),(537,612),(361,279),(361,280),(270,279),(270,280),(15,167),(15,9),(15,93),(1,10),(1,9),(21,32),(21,33)]
models={}
for p,c in pairs:
 prefix='slice' if p==21 else 'thread'
 m=f'PV_LIB_B_F{p}_F{c}'+('Fixed' if p in [15,1] else '')
 models[f'{prefix}:f{p} -> {prefix}:f{c}']=m
facet_rows={'slice:f0 :: entryReferenceValidity':'slice:f0','thread:f361 :: nameValidity':'thread:f270','thread:f6 :: machineTransport':'thread:f6','thread:f361 :: arcCloneValueFrame':'thread:f361','thread:f361 :: atomicCounts':'thread:f361','slice:f7 :: typedDrop178':'slice:f7','thread:OwnInit :: numbering':'thread:OwnInit','thread:OwnInit :: registryFrame':'thread:OwnInit','thread:OwnInit :: resourceEnv':'thread:OwnInit'}
receipts={}
for p in E.glob('receipt-*.json'):
 r=json.loads(p.read_text())
 if r.get('accepted') and not r.get('runtime_audit'):receipts[r['target']]=r
slots=[]
for s in old['slots']:
 if s['status']=='INSTANTIATED':continue
 key=s['slot'];o=dict(slot=key,parent=s['parent'],child=s['child'],sites=s['sites'],before_status=s['status'],merged_status=current[key]['status'])
 if key in models:
  m=models[key];p=pathlib.Path('lean',m+'.lean');r=receipts.get(m)
  roots=re.findall(r'^#print axioms (\S+)',p.read_text(),re.M)
  actual=[m+'.'+t for t in roots if t.startswith('actual_machine')]
  o.update(status='INSTANTIATED',module=m,theorem=actual[0],theorems=actual,model=m+'.model',law=m+'.law',caller_domain=m+'.caller_domain',root=s['root'],source=str(p),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),compiled=bool(r),attempt=r['attempt'] if r else None,graph_of_function=True,raw_audited=False)
  if s['parent']=='slice:f21':
   qualification='Exact existing CLOSED-provider deterministic supplied-machine run; issued scalar/fresh-activation domain is proved. No first-boundary strengthening. The actual preceding f21 invariant and literal-machine adequacy remain row/composition obligations.'
  elif s['parent'] in ['thread:f15','thread:f1']:
   qualification='Exact source-selected token/operands and fixed named writer projection on corrected OWNER-aware machine. CLOSED full-reply certificate retained separately; no arbitrary Post is installed as the law. Invalid decode is explicit undefined. Actual caller provenance/initialization and native/source value adequacy remain row obligations.'
  elif s['parent']=='thread:f170':
   qualification='Existing literal CLOSED graph and checked source-store poll adapter reused by name. Caller owner/freshness domain derived from actual operand evaluation. Existing named memory/source semantics retained; continuous f170 composition and native/source adequacy remain row obligations.'
  else:
   qualification='Exact literal polymorphic callee token, provider generic administration graph, all replies and full local delivery frame. Representative CLOSED certificate separately retained without equating generic metadata. Source-store interpreter native poll adapter proved. Native/source value adequacy and continuous caller composition remain row obligations; no v2 OwnInit history claim.'
  o['qualification']=qualification
 elif key in corrections:
  o.update(corrections[key]);m=o['module'];o['raw_audited']=False if m.startswith('PV_LIB_B_') else 'reused-existing-evidence'
  if m.startswith('PV_LIB_B_'):
   r=receipts.get(m);o.update(compiled=bool(r),attempt=r['attempt'] if r else None)
 else:
  assert s['status']=='MISSING-CHILD-LEMMA'
  waiting=facet_rows[key] if key in facet_rows else s['child']
  o.update(status='WAITING-ON-ROW',waiting_on_row=waiting,module=None,theorem=None,proof_attempted=False,reason='The complete caller/provider obligation waits for this paused row. No row proof attempted; existing compiled support is retained separately.')
  if current[key].get('instance'):o['retained_support']=current[key]['instance']
  if key in facet_rows:o['facet_owner_reason']='Caller-domain/native/representation composition, not a new CLOSED provider root.'
 slots.append(o)
assert len(slots)==60
counts=dict(collections.Counter(s['status'] for s in slots));assert counts=={'INSTANTIATED':16,'WAITING-ON-ROW':39,'CORRECTED-STATEMENT':5},counts
x=dict(schema=1,session=5,lane='B',branch='codex/pv-lib-slice-20261107',start_head='6db830678863f2d0baf4ee5b3182310f9f7a0206',single_start_merge=MERGE,assignment_snapshot=BASE,assignment_counts=old['counts'],merged_counts=merged['counts'],counts=counts,shared_map_edited=False,ledger_rows_closed=0,endpoint_premises_removed=0,endpoint_premises_added=0,new_trust_fields=0,owninit_joint_witness_work=False,qualification='Library graph/caller-domain/local-machine adapters only. INSTANTIATED has the same qualified meaning as existing map entries, not source/binary adequacy or parent-row closure. Historical support/evidence is retained. See NOTES.md for the typedDrop178 residual facet.',slots=slots)
audit_path=E/'RAW_AUDIT.json'
if audit_path.exists():
 audit=json.loads(audit_path.read_text()); audited={r['root'] for r in audit['roots']}
 for o in slots:
  if o.get('module','') and o['module'].startswith('PV_LIB_B_'):
   assert o['theorem'] in audited
   o.update(raw_audited=True,audit_attempt=audit['attempt'])
 x['audit']=dict(path=str(audit_path),attempt=audit['attempt'],root_count=audit['root_count'],exit=audit['receipt']['exit'])
(E/'MAP-DELTA-S5.json').write_text(json.dumps(x,indent=2)+'\n')
print(counts)
