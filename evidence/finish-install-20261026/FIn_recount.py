"""Recount immutable ledgers, retaining native/source-global scope distinctions."""
from pathlib import Path
from collections import Counter
import hashlib,json,copy
P=Path(__file__).resolve().parent; R=P.parents[1]
removed={f'F3Y_G_L{n}' for n in (133,134,135,136,137,138,147)}
aliases={'L137':'L134','F3Y_G_L137':'F3Y_G_L134'}
def counts(rows):
    return {name:dict(Counter(r['classification'] for r in rows if pred(r)))
      for name,pred in [('actual',lambda r:r['scope']=='actual antecedent'),
       ('actual_plus_nonalias_deployment',lambda r:r['scope']!='deployment alias')]}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
result={'method':'Expand actual family predicates, distinguish native and source-global witnesses, exclude deployment aliases, then identify identical quarter predicates. No trust or numeric assumptions reclassified.',
 'removed_historical_global_rows':sorted(removed),'distinct_P_delta':-6,
 'quarter_aliases':aliases,'alias_evidence':'FIn_070/stdout.log; RoundLaws.quarter is independent of bytes/poly, same ops and outer guards.',
 'no_added_T_P_C':True,'native_premise_delta':0,'ledgers':{}}
for name,path in [('headline','evidence/frozen3-head6-20261026/F3Y_premises.json'),('native','evidence/recount6-20261026/Rc6_premises.json')]:
    p=R/path;old=json.loads(p.read_text());rows=old['rows']
    ids={r['id'] for r in rows}
    before=copy.deepcopy(rows)
    after=[r for r in copy.deepcopy(rows) if name!='headline' or r['id'] not in removed]
    corrected_before=[r for r in before if r['id'] not in aliases]
    corrected_after=[r for r in after if r['id'] not in aliases]
    assert name!='headline' or removed<=ids
    result['ledgers'][name]={'source':path,'sha256':digest(p),
      'historical_raw_before':counts(before),'historical_raw_after':counts(after),
      'alias_corrected_before':counts(corrected_before),'alias_corrected_after':counts(corrected_after),
      'rows':[dict(r,finish_install_status=('removed from specialised headline' if name=='headline' and r['id'] in removed else 'alias of '+aliases[r['id']] if r['id'] in aliases else 'retained')) for r in before]}
b=(P/'FIn_Headline-statement.lean.txt').read_text()
a=(P/'FIn_ReducedHeadline-statement.lean.txt').read_text()
assert b==a.replace('FIn_GlobalOwners.Owners','F3Y_PreparedAt.Owners')
result['statement_comparison']={'identical_after_only_owner_predicate_substitution':True,
 'before_sha256':digest(P/'FIn_Headline-statement.lean.txt'),
 'after_sha256':digest(P/'FIn_ReducedHeadline-statement.lean.txt')}
assert result['ledgers']['headline']['alias_corrected_before']['actual']=={'T':83,'P':41}
assert result['ledgers']['headline']['alias_corrected_after']['actual']=={'T':83,'P':35}
assert result['ledgers']['native']['alias_corrected_before']['actual']=={'T':83,'P':31}
(P/'FIn_recount.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:{f:v for f,v in x.items() if 'before' in f or 'after' in f} for k,x in result['ledgers'].items()},indent=2))
