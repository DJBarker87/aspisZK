"""Negative controls for the additive evidence gates, no theorem/native credit."""
from pathlib import Path
import json,copy,collections
E=Path(__file__).resolve().parent;J=lambda n:json.loads((E/n).read_text())
a=J('NGK_AUDIT.json');s=J('NGK_SCAN.json');d=J('NGK_LEDGER_DELTA.json');m=J('NGK_AUDIT_ROOTS.json');assoc=J('NGK_CERT_ASSOCIATIONS.json');sm=J('NGK_STATEMENT_MANIFEST.json')
def check(a,s,d,assoc):
 assert a['standard_axioms_only'] and len(a['roots'])==a['root_count']==len(m['roots'])
 assert collections.Counter(r['root'] for r in a['roots'])==collections.Counter(m['roots'])
 assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in a['roots'])
 assert len(a['fixture_results'])==8 and all(r['equal'] for r in a['fixture_results'])
 assert [r['walked_axioms'] for r in a['fixture_results']]==[['NEP_Planted.matchAx'],['NEP_Planted.privateAx'],['NEP_Planted.proofAx'],['NEP_Planted.auxAx'],[],[],[],[]]
 assert a['all_batches_same_binary']
 assert s['status']=='PASS' and s['dangling']==s['incompatible_owners']==s['import_mismatches']==0
 assert not s['legacy_bad_owner_modules_loaded']
 assert d['rows']==[] and d['composed_rows_added']==d['closed_by_this_job']==0
 assert d['after']==d['before']==dict(Pool_production_association='OPEN',B='OPEN',D='OPEN')
 assert collections.Counter(r['name'] for r in assoc['entries'])==collections.Counter(r['name'] for r in sm['records'])
 for r in sm['records']:assert next(x for x in assoc['entries'] if x['name']==r['name'])['owner']=='NGK_'+r['source_module']
check(a,s,d,assoc)
mutations=[('nonstandard axiom',0,lambda x:x['roots'][0]['walked_axioms'].append('forbiddenAx')),('missing raw root',0,lambda x:x['roots'].pop()),('duplicate raw root',0,lambda x:x['roots'].__setitem__(0,x['roots'][1])),('missed fixture axiom',0,lambda x:x['fixture_results'][0].__setitem__('walked_axioms',[])),('mutated fixture contamination',0,lambda x:x['fixture_results'][4].__setitem__('walked_axioms',['NEP_Planted.matchAx'])),('different proof binary',0,lambda x:x.__setitem__('all_batches_same_binary',False)),('dangling reference',1,lambda x:x.__setitem__('dangling',1)),('incompatible owner',1,lambda x:x.__setitem__('incompatible_owners',1)),('import mismatch',1,lambda x:x.__setitem__('import_mismatches',1)),('legacy owner loaded',1,lambda x:x['legacy_bad_owner_modules_loaded'].append('PreparedFromQmSourceBridge')),('unsound Pool promotion',2,lambda x:x.__setitem__('closed_by_this_job',1)),('B falsely closed',2,lambda x:x['after'].__setitem__('B','CLOSED')),('missing theorem association',3,lambda x:x['entries'].pop()),('wrong theorem owner',3,lambda x:x['entries'][0].__setitem__('owner','legacy'))]
results=[]
for name,i,mutate in mutations:
 args=copy.deepcopy([a,s,d,assoc]);mutate(args[i])
 try:check(*args)
 except AssertionError:results.append(dict(name=name,rejected=True))
 else:raise AssertionError(name)
(E/'NGK_TESTS.json').write_text(json.dumps(dict(positive=True,mutations=results,all_rejected=True),indent=1)+'\n');print(len(results),'mutations rejected')
