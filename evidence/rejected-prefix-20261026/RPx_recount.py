"""Ledger-family recount for the same Rc7 premises, with exact before/after evidence."""
from pathlib import Path
from collections import Counter
import json,hashlib,re,copy
E=Path(__file__).resolve().parent;R=E.parents[1]
load=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=load(R/'evidence/recount7-20261026/Rc7_premises.json')
plan=load(E/'RPx_audit_plan.json');catalog={};audits=[]
for item in plan:
    d=E/item['attempt'];rec=load(d/'receipt.json');assert rec['exit_status']==0,item
    assert rec['source_hashes'][item['module']+'.lean']==sha(R/'lean'/(item['module']+'.lean'))
    s=(d/'stdout.log').read_text()
    audits.append(dict(**item,stdout_sha256=sha(d/'stdout.log'),source_sha256=sha(R/'lean'/(item['module']+'.lean'))))
    for b in re.split(r'(?=^structure )',s,flags=re.M):
        if not b.startswith('structure ') or 'fields:\n' not in b:continue
        key=re.match(r'structure (\S+)',b)[1]
        fields=b.split('fields:\n',1)[1].split('constructor:',1)[0]
        catalog[key]=dict(fields=fields,field_names=re.findall(r'^  ([\w.α-ωΑ-Ω]+) :',fields,re.M))
previous=load(R/'evidence/recount7-20261026/Rc7_field_catalog.json')
compared=[]
for k in catalog.keys() & previous.keys():
    assert catalog[k]['fields']==previous[k]['fields'],('changed inherited family',k)
    compared.append(k)
assert len(compared)>=30,len(compared)
root=(E/'RPx_054/stdout.log').read_text()
def statement(name):
    a=root.index('@AspisR1.'+name+' :');b=root.find('\n@AspisR1.',a+1)
    return root[a:b if b>=0 else len(root)].split("\n'AspisR1.",1)[0].rstrip()+'\n'
for name,label in [('Rc7_Top.deployed','BEFORE'),('RPx_Top.deployed','AFTER'),('RPx_Nonvacuity.composed','NONVACUITY'),('RPx_AccountBudget.budget','ACCOUNT_BUDGET'),('RPx_AccountCharge.charged','ACCOUNT_CHARGE')]:
    (E/('RPx_'+label+'.lean.txt')).write_text(statement(name))
(E/'RPx_BOUNDARY.lean.txt').write_text((E/'RPx_055/stdout.log').read_text())
before=(R/'lean/Rc7_Top.lean').read_text();after=(R/'lean/RPx_Top.lean').read_text()
def binders(s):return s[s.index('theorem deployed'):s.index('    :\n',s.index('theorem deployed'))]
assert binders(before)==binders(after),'changed top hypotheses/quantifiers'
assert 'exact Rc7_Top.deployed' in after
for term in ['RPx_Transport.Claims','RPx_NativeTransport.PrefixBound','CPH_Recorder.Facts','F3T_Runtime.StoredCarrierBinding']:
    assert term in after,term
rows=copy.deepcopy(old['rows'])
for row in rows:
    if row['id']=='L181':
        row.update(running_job='RPx_',status='retained',blocker='Installed per-body source/account logs and duplicate-aware charges proved; reified original native wrapper attempted prefixes and adaptive account Q proved. Complete physical/native/runtime rejected-history association with the SAME headline F3X account remains. Accepted returned-run binding alone permits arbitrary outer query prefixes. Result erasure is not physical log equality.',evidence='RPx_Transport; RPx_NativeTransport; RPx_AccountBudget; RPx_AccountCharge; RPx_Obstruction; RPx_Top')
assert len(rows)==len(old['rows'])
scopes=['actual antecedent','deployment only','deployment alias']
counts={}
for scope in scopes:
    selected=[r for r in rows if r['scope']==scope]
    counts[scope]={k:sum(r['classification']==k for r in selected) for k in ['T','P','G','C']}
    assert counts[scope]==old['counts'][scope]['classes']
nonalias=[r for r in rows if r['scope']!='deployment alias']
counts['deduplicated actual plus non-alias deployment']={k:sum(r['classification']==k for r in nonalias) for k in ['T','P','G','C']}
assert counts['deduplicated actual plus non-alias deployment']=={'T':89,'P':31,'G':13,'C':0}
out=dict(actual_theorem='AspisR1.RPx_Top.deployed',baseline='AspisR1.Rc7_Top.deployed',method=old['method'],classification_citation=old['classification_citation'],counts=counts,rows=rows,removed_rows=[],added_rows=[],reclassified_rows=[],delta={k:{c:0 for c in ['T','P','G','C']} for k in counts},statement_evidence=audits,unchanged_fresh_structure_inventories=sorted(compared),inherited_audits=load(E/'RPx_inherited_audits.json'),binding_sha256=hashlib.sha256(binders(after).encode()).hexdigest(),caveat='No premise removed. Extra proved output facts are not premise discharges. L181 remains; no physical-source counterexample or 100-bit release claim.')
(E/'RPx_premises.json').write_text(json.dumps(out,indent=2)+'\n')
(E/'RPx_field_catalog.json').write_text(json.dumps(catalog,indent=2)+'\n')
print(json.dumps(dict(counts=counts,delta='zero',fresh_unchanged_structures=len(compared))))
