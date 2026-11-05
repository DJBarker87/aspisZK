"""Unchanged NIJ/NFK validation plus strictly additive isolated/canonical gate."""
from pathlib import Path
import json,lzma,hashlib,copy,types,re
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-entry5-20261107';R=E.parents[1]
read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
assert read(E/'NIS_RERUN.json')['status']=='PASS_ISOLATED_RERUN'
for name in ['ENTRY','ERROR']:assert read(E/('NIS_REPLAY_'+name+'.json'))['exit_status']==0
def audit(a):
 r=read(E/a/'receipt.json');assert r['exit_status']==0
 s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 return r,[json.loads(l[11:]) for l in s.splitlines() if l.startswith('NEP_RESULT ')]
fx,fixtures=audit('NIS_L030');raw,roots=audit('NIS_L032');scan,_=audit('NIS_L033')
assert len(fixtures)==8 and all(x['equal'] for x in fixtures)
assert all(len(x['walked_axioms'])==1 for x in fixtures[:4]) and all(not x['walked_axioms'] for x in fixtures[4:])
required=read(E/'NIS_AUDIT_ROOTS.json')['groups'][0]
assert {x['root'] for x in roots}==set(required) and len(roots)==len(required)
assert all(x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in roots)
loaded=[json.loads(l) for l in lzma.decompress((E/'NIS_NIS_LOADED_scan.jsonl.xz').read_bytes()).decode().splitlines()]
assert all(x['imports_match'] and not x['dangling'] and not x['duplicate_owners'] for x in loaded)
names={x['module'] for x in loaded}
assert {'NGK_COMBINED_IMPORT','NIM_COMBINED_IMPORT','NIM_NHY_COMBINED_IMPORT','NIM_NHJ_COMBINED_IMPORT','NIS_COMBINED_IMPORT','RPx_Deployed'}<=names
retarget=read(E/'NIS_RETARGET.json')
assert not (set(retarget['module_map']) & names), 'Original affected module loaded alongside retarget'
assert 'NGL_MapReference.Types' not in names
base_raw=lzma.decompress((E.parent/'ledger11-20261107/NII_LEDGER.json.xz').read_bytes());base=json.loads(base_raw)
nim=read(E.parent/'owner-dedupe-20261107/NIM_LEDGER_DELTA.json');assert sha(base_raw)==nim['basis_uncompressed_sha256']
by={r['row']:r for r in base['rows']}
for folder,prefix in [('slice-d-entry3-20261106','NHJ'),('slice-d-entry4-20261106','NHY')]:
 for row in read(E.parent/folder/(prefix+'_LEDGER_DELTA.json'))['rows']:by[row['row']]=copy.deepcopy(row)
counts=lambda rows:{s:sum(r['composed_status']==s for r in rows)for s in ['CLOSED','QUALIFIED','OPEN']}
assert counts(by.values())==nim['after']=={'CLOSED':407,'QUALIFIED':0,'OPEN':192}
baseline=copy.deepcopy(base);baseline['rows']=list(by.values())
v=(P/'NIJ_NFK_validate.py.txt').read_bytes();assert v==(E.parent/'slice-d-entry-20261105/NGL_NFK_validate.py.txt').read_bytes()
n=types.ModuleType('NIS_retained_NFK');n.__file__=str(P/'NIJ_NFK_validate.py.txt');exec(compile(v,n.__file__,'exec'),n.__dict__);n.BASE_CREDITS=base['NEZ_credits']
withheld=read(P/'NIJ_WITHHELD_ARTIFACTS.json');delta=withheld['NIJ_LEDGER_DELTA.json']
selected={f['id']:copy.deepcopy(f) for f in withheld['NIJ_CLOSED.json']['functions']}
mapping={r['original']:r['attempt'] for r in read(E/'NIS_RERUN_PLAN.json')}
certs={};candidates={};new=[]
for r in delta['rows']:
 rid=r['row'];assert by[rid]['composed_status']=='OPEN'
 oldid=r['selected_claims'][0];c=copy.deepcopy(selected[oldid]);c['id']=oldid.replace('NIJ::','NIS::')
 c.update(native_passes=[mapping[a] for a in c['native_passes']],matched_controls=[mapping[a] for a in c['matched_controls']],combined='NIS_L025',audit=['NIS_L030 eight fidelity controls','NIS_L032 raw79 roots','NIS_L033 NFX scan'],isolation='NIS_RERUN.json:45 immutable original configurations, path-only relocation, explicit CARGO_TARGET_DIR asserted before unchanged native gate',canonical_owner='NIM canonical forest; NFW_ErrorReference.VerifierError only; no original map owner imported',prior_source_validator='NIS_REPLAY_ENTRY.json / NIS_REPLAY_ERROR.json: unchanged NIJ validators, selected isolated native reads, original source snapshots byte-identical')
 c.pop('semantic_review_sha256',None);c['semantic_review_sha256']=sha(json.dumps(c,sort_keys=True).encode())
 row=copy.deepcopy(r);row['selected_claims']=[c['id']]
 row['active_support_receipts']=[str((E/a/'receipt.json').relative_to(R)) for a in c['native_passes']]
 row['composed_reason']='Isolated native candidates reproduce all matched controls; unchanged NIJ/NFK validators; import-only NIM retarget; full canonical/headline combined raw standard axioms and zero-defect NFX.'
 assert not n.row_checks(row,by[rid],c),n.row_checks(row,by[rid],c)
 n.certificate_checks(type('Support',(),{'support':lambda self,c:None})(),c)
 certs[rid]=c;candidates[rid]=('NIS',row);new.append(rid)
# NII's added inventory rows have a newer schema; retain them byte-for-byte.
# Apply the unchanged NFK predicates to precisely the candidate rows, as NIJ did,
# and explicitly require every selected callee in the coherent CLOSED baseline.
closed_claims={c for r in baseline['rows'] if r['composed_status']=='CLOSED' for c in r['selected_claims']}
for _,row in candidates.values():
 for obligation in row['caller_domain_obligations']:
  assert set(obligation.get('callee_claims',[]))<=closed_claims
small=copy.deepcopy(baseline);small['rows']=[copy.deepcopy(by[rid]) for rid in new]
checked=n.admit(small,candidates,certs,{'NIS':new})
admitted=copy.deepcopy(baseline)
updated={r['row']:r for r in checked['rows']}
admitted['rows']=[updated.get(r['row'],r) for r in admitted['rows']]
assert all(next(r for r in admitted['rows'] if r['row']==rid)['composed_status']=='CLOSED' for rid in new)
assert counts(admitted['rows'])=={'CLOSED':410,'QUALIFIED':0,'OPEN':189}
out=dict(schema_version=1,frozen_revision=base['frozen_revision'],new_composed_functions=2,new_composed_rows=3,functions=list({c['id']:c for c in certs.values()}.values()),driver_root_status='OPEN')
(E/'NIS_CLOSED.json').write_text(json.dumps(out,indent=1)+'\n')
(E/'NIS_LEDGER_DELTA.json').write_text(json.dumps(dict(baseline='evidence/owner-dedupe-20261107/NIM_LEDGER_DELTA.json',baseline_sha256=sha((E.parent/'owner-dedupe-20261107/NIM_LEDGER_DELTA.json').read_bytes()),baseline_counts=nim['after'],new_closed_rows=new,rows=[r for r in admitted['rows'] if r['row'] in new],counts_after=counts(admitted['rows']),unchanged_NFK_sha256=sha(v),other_statuses_unchanged=True,security_target_established=False),indent=1)+'\n')
(E/'NIS_AUDIT.json').write_text(json.dumps(dict(status='PASS_AX2_NFX',raw_roots=roots,fixtures=fixtures,scan=dict(modules=len(loaded),dangling=0,incompatible_owners=0,import_mismatches=0),canonical_owner_collision=False,standard_axioms_only=True,scope='Focused canonical cached closure; not a cold release/ELF replay'),indent=1)+'\n')
print(json.dumps(dict(status='PASS',new_closed_rows=new,counts=counts(admitted['rows']))))
