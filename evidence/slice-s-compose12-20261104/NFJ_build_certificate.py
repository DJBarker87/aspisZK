from pathlib import Path
import sys,json,re
import NFJ_validate as v
E=v.E;R=v.R
base=v.baseline()
by={}
for r in base['rows']:by.setdefault(r['function'],[]).append(r)
root=by[v.F][0]
def pin(p):return dict(path=str(p.relative_to(R)),sha256=v.sha(p.read_bytes()))
ts=[]
for module,attempt,namespace in [('NFJ_Comparison','NFJ_L001','NFJ_Comparison'),('NFJ_Scanner','NFJ_L003','NFJ_Scanner')]:
 source=E/attempt/'NFJ_SOURCE.lean.txt';text=source.read_text()
 for m in re.finditer(r'^theorem (\w+)\b',text,re.M):
  end=text.index(' :=',m.start());statement=text[m.start():end]
  ts.append(dict(name=namespace+'.'+m[1],source=pin(source),receipt=pin(E/attempt/'receipt.json'),snapshot_path='NFJ_generated/'+module+'.lean',statement=statement,statement_sha256=v.sha(statement.encode())))
assert [t['name'] for t in ts]==v.NAMES
c=dict(id='NFJ_scanner',kind='root-composition',subject=v.F,frozen_revision=v.REV,inner_hypotheses_remaining=[],hypotheses=v.HYPOTHESES,trust_classification='P6/D188 option A reclassification; uses RuntimeMemcmp (ac), ADDED trust',new_trust_rows=[v.TRUST],runtime_contract='RuntimeMemcmp688Zero',domain_theorems=ts,physical_theorems=ts,source_association=v.all_native(),required_obligations=[o['id'] for o in root['caller_domain_obligations']],primitive_certificates=v.PRIMITIVES,native_certificate=dict(complete=True,domain='all valid immutable slices, arbitrary raw bytes and length; all Result and rejection paths',positive=['NFJ_K003','NFJ_K011','NFJ_K013'],controls=[f'NFJ_K{n:03}' for n in [4,5,6,7,8,9,10,12,14]],inherited='NFD_K134..150; no root credit from supports alone',no_writable_static=True,no_function_pointer=True),runtime_domain=dict(left='SAME retained successful encoder reply allocation',right='SAME retained header allocation bytes[0..688]',left_length=688,right_length=688,length_argument=688,reply='SAME supplied local i32 slot',observation='zero only',other_slot_observers=[],equal_continuation='frozen tag test and same candidate/proof_length return',unequal_continuation='frozen InvalidAccountData',completion='NFH_ComparisonDomain.complete688_association/complete688_on_domain'))
c.update({k:True for k in v.FLAGS});c['edges']=sorted(v.F+' -> '+g for g in root['canonical_callees']);c['call_domain_certificates']={}
for edge in c['edges']:
 g=edge.split(' -> ')[1]
 names={h['name'] for r in by[g] for h in r['named_hypotheses']}|{h for o in root['caller_domain_obligations'] if o.get('callee')==g for h in o['required_named_hypotheses']}
 d=dict(subject=edge,classification=v.CLASSIFICATIONS[g],inner_names_discharged=sorted(names),inner_hypotheses_remaining=[],selected_callee_claims=sorted({x for r in by[g] for x in r['selected_claims']}),domain_theorems=ts,physical_theorems=ts)
 d.update({k:True for k in v.FLAGS});c['call_domain_certificates'][edge]=d
c['support']=[pin(R/p) for p in sorted(v.support_paths())]
c['semantic_review_sha256']=v.sha(json.dumps(c,sort_keys=True).encode())
p=dict(inherits='evidence/slice-s-compose11-20261104/NFH_LEDGER_DELTA.json',NFJ_certificates={v.F:c})
(E/'NFJ_LEDGER_DELTA.json').write_text(json.dumps(p,indent=1)+'\n')
assert v.certificate(c,base),'new certificate rejected'
v.main(base)
