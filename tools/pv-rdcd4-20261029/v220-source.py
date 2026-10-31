"""V220 own-1 source census. This is not an original checker or extraction."""
from pathlib import Path
import json,subprocess,hashlib,re
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-rdcd4-20261029'
def sha(b):return hashlib.sha256(b).hexdigest()
def tracked(p):return subprocess.check_output(['git','show','HEAD:'+p],cwd=R)
old=json.load(open(R/'evidence/pv-rdcd3-20261028/v217-field-source-result.json'))
field=[]
for x in old['records']:
 p='crates/aspis-core/src/'+('field/ct.rs' if x['path'].endswith('/ct.rs') else 'field.rs')
 b=tracked(p); assert sha(b)==x['source_sha256'],p
 field.append(dict(x,path=p,model=x['model'].replace('PV_RDCD3_FieldSource','PV_RDCD4_FieldSource'),reuse='whole deployed file unchanged; source statement binding retained'))
a=tracked('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RDCD3_FieldSource.lean').decode()
b=tracked('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RDCD4_FieldSource.lean').decode()
assert b.startswith(a.replace('PV_RDCD3_FieldSource','PV_RDCD4_FieldSource'))
lib={x['relative']:x for x in json.load(open(E/'library-sources.json'))}
rs=json.load(open(R/'evidence/pv-rdcd3-20261028/range-source-result.json'))
for x in rs['records']:
 rel=x['path'].split('/library/core/src/')[1]; assert lib[rel]['sha256']==x['file_sha256']
env=json.load(open(R/'evidence/pv-rdcd3-20261028/rows/V220-envelope.json'))
records=[]
for i,x in enumerate(env['unresolved']):
 if i<10: disposition='historical comparator; not a deployed body'
 elif i in [12,13]:disposition='reached Range<usize>::next; source nested channel loop, concrete TrustedStep specialization'
 elif i==14:disposition='reached TrustedStep usize spec_next; general Step branch not instantiated'
 elif i in [10,11]:disposition='unreachable panic formatting: all fixed array indices and loop bounds valid; release debug assertions disabled, arithmetic wraps'
 else:disposition='excluded BTree typed receiver; actual receiver is core::ops::Range<usize>'
 records.append(dict(index=i,record=x,disposition=disposition))
out=dict(row='V220',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),field_bindings=field,field_model_namespace_only_transport=dict(old_sha256=sha(a.encode()),new_sha256=sha(b.encode())),range_bindings=rs['records'],records=records,counts=dict(historical=10,reached=3,excluded_typed=5,excluded_guard=2),profile='ct-host-prover, release debug_assertions=false overflow_checks=false; inherited exact deployed graph',b3p6_1_credit=0,original_checker='UNRECOVERED; no source census is relabelled a checker',status='partial source closure; lazy/root complete-body literals and whole-row Result bridge pending',retained=['V370/D381/D386','E1/E2','native RunJoin/world/physical observer','client route','L1/L2/L3','T unchanged'])
(E/'v220-source-census.json').write_text(json.dumps(out,indent=2)+'\n')
print('V220:26 unchanged field bodies,8 unchanged range/index bodies;20 records dispositioned,3 deployed range records reached. Partial only.')
