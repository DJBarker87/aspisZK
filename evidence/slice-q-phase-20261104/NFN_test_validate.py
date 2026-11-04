"""Negative admission controls; never mutate proved inputs on disk."""
from NFN_validate import *
old=obj(O/'NFG_LEDGER_DELTA.json');a=obj(E/'NFN_AUDIT.json');d=obj(E/'NFN_LEDGER_DELTA.json');assert d==expected(old,a)
results=[]
def reject(name,action):
 try:action()
 except (AssertionError,KeyError):results.append(dict(test=name,status='PASS_REJECTED'));return
 raise AssertionError('mutation admitted: '+name)
for field in ['dangling','duplicate_owners','import_mismatches']:
 x=copy.deepcopy(a);x['incoherence_scan'][field]=1
 reject('reject '+field,lambda x=x:own_checks(x))
x=copy.deepcopy(a);x['results']=[r for r in x['results'] if r['root']!='AspisR1.RPx_Deployed.deployed'];reject('reject missing headline raw walk',lambda:own_checks(x))
x=copy.deepcopy(a);x['fixtures']=x['fixtures'][:-1];reject('reject missing fixture',lambda:own_checks(x))
x=copy.deepcopy(a);x['results'][0]['walked_axioms']=['sorryAx'];reject('reject nonstandard axiom',lambda:own_checks(x))
for name,mut in [('reject double counted source rows',lambda x:x.update(total_closed=x['total_closed']+2)),('reject query_loop promotion',lambda x:x['promotions'].append(dict(row='TX1:182',after='CLOSED'))),('reject hidden edge deletion',lambda x:x.update(edge_total=x['edge_total']-1)),('reject missing geometry row',lambda x:x['promotions'].pop())]:
 x=copy.deepcopy(d);mut(x)
 def eq():assert x==expected(old,a)
 reject(name,eq)
(E/'NFN_TESTS.json').write_text(json.dumps(results,indent=1)+'\n');print(json.dumps(results))
