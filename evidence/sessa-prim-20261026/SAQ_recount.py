"""Reviewed atomic correspondence, mechanically recounted; not a proof checker."""
import collections,copy,hashlib,json
from pathlib import Path
base=Path('evidence/recount2-20261026/Rc2_premises.json')
out=Path('evidence/sessa-prim-20261026')
b=json.loads(base.read_text())
ids={f'N{i:03}' for i in range(47,108)}
removed=[copy.deepcopy(r) for r in b['rows'] if r['id'] in ids]
assert len(removed)==61
assert all(r['classification']=='P' and r['owner']=='session A' and r['scope']=='actual antecedent' for r in removed)
for r in removed:
 r['baseline_status']=r['status']
 r['status']='derived at SAQ source-selected instance; generic Rc2 unchanged'
remaining=[r for r in b['rows'] if r['id'] not in ids]
def count(rows):
 return {'rows':len(rows),'classes':dict(collections.Counter(r['classification'] for r in rows)),
         'owners':dict(collections.Counter(r['owner'] for r in rows))}
scopes={'actual antecedent':lambda r:r['scope']=='actual antecedent',
        'all retained audit rows':lambda r:True,
        'deduplicated actual plus non-alias deployment':lambda r:r['scope']!='deployment alias'}
result={'actual_generic_theorem':'AspisR1.Rc2_Top.deployed','actual_generic_delta':0,
 'selected_replacement':'AspisR1.SAQ_CompleteTop.deployed',
 'selected_dictionary':'SAQ_CompleteInstall.configuration indexError c reservation',
 'baseline_sha256':hashlib.sha256(base.read_bytes()).hexdigest(),
 'method':'Rc2 atomic conjunctive leaves, quantified families, SAME witnesses/guards, shared-dictionary deduplication. Correspondence is explicitly reviewed; kernel proof and transcript are separate evidence.',
 'selected_removed':removed,'selected_added_proof_rows':[],
 'new_data_parameter':'indexError : CoreError selects the source IndexOutOfRange constructor; existing carrier and extraction/native association remain.',
 'counts':{n:{'before':count([r for r in b['rows'] if f(r)]),'selected_after':count([r for r in remaining if f(r)])} for n,f in scopes.items()},
 'retained_rows':remaining,
 'no_native_credit':'L178 and existing native/extraction/P6/source-to-ELF boundaries are retained. Generic Rc2 totals are unchanged until selected-instance integration.'}
(out/'SAQ_recount.json').write_text(json.dumps(result,indent=2)+'\n')
assert result['counts']['actual antecedent']['selected_after']['classes']=={'T':82,'P':110}
assert result['counts']['deduplicated actual plus non-alias deployment']['selected_after']['classes']=={'T':88,'P':123}
print(json.dumps({k:v for k,v in result.items() if k in ['actual_generic_delta','counts']}))
