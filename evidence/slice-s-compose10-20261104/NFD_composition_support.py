"""Shared additive certificate bookkeeping, never a semantic admission by itself."""
import json
import NFD_validate as v
from NFD_build_certificates import ref
from NFD_bridge_checks import FLAGS,SPEC,REV
E=v.E;R=v.R
def source(patch,name):
 frag=patch.split('+++ b/programs/r1-cost-probe/src/'+name+'.rs\n',1)[1].split('--- a/',1)[0]
 return '\n'.join(l[1:] for l in frag.splitlines() if l.startswith('+'))+'\n'
def support(attempts,extras):
 paths={E/n for n in extras}
 for a in attempts:
  names=[a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-shape.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'-frozen-identity.json',a+'-rule16-check.json',a+'-metadata-pin.json',a+'-NFD_native_contracts.patch',a+'-NFD_oracle.patch']
  archive=a+'-inputs.json' if (E/(a+'-inputs.json.xz')).exists() else 'NFD_SOURCE_HISTORY.json'
  paths.update(E/n for n in names+[archive+'.xz',archive+'.sha256'])
 return [ref(p) for p in sorted(paths)]
def seal(c):
 c['semantic_review_sha256']=v.sha(json.dumps({k:w for k,w in c.items() if k!='semantic_review_sha256'},sort_keys=True).encode());return c
def make(f,n,thms,base,attempts,extras,classification,trust=[]):
 by={}
 for r in base['rows']:by.setdefault(r['function'],[]).append(r)
 c=dict(id='NFD_'+f.rsplit('::',1)[-1],subject=f,kind='root-composition' if f in SPEC['roots'] else 'member-composition',frozen_revision=REV,native_certificate=n,domain_theorems=thms,physical_theorems=thms,support=support(attempts,extras),required_obligations=[o['id'] for r in by[f] for o in r['caller_domain_obligations']],edges=[e for e in SPEC['internal_edges'] if e.startswith(f+' -> ')],call_domain_certificates={},hypotheses=[f+'.PacketDomain',f+'.PhysicalInterpretation','RuntimePersistence','CompositionTrustOptionA']+trust,new_trust_rows=trust,inner_hypotheses_remaining=[],trust_classification='P6/D188 option A reclassification')
 c.update({k:True for k in ['exact_callsite',*FLAGS]})
 for edge in c['edges']:
  g=edge.split(' -> ')[1]
  d=dict(subject=edge,classification=classification,selected_callee_claims=list(dict.fromkeys(x for r in by[g] for x in r['selected_claims'])),inner_names_discharged=list(dict.fromkeys([h['name'] for r in by[g] for h in r['named_hypotheses']]+[h for r in by[f] for o in r['caller_domain_obligations'] if o.get('callee')==g for h in o['required_named_hypotheses']])),domain_theorems=thms,physical_theorems=thms,inner_hypotheses_remaining=[])
  d.update({k:True for k in FLAGS});c['call_domain_certificates'][edge]=d
 return seal(c)
def structural(c,f,thms,base,attempts,extras,classification,trust=[]):
 assert c['kind']==('root-composition' if f in SPEC['roots'] else 'member-composition')
 assert c['native_certificate']['function']==f and c['native_certificate']['complete'] is True
 assert [t['name'] for t in c['domain_theorems']]==thms and c['physical_theorems']==c['domain_theorems']
 expected=make(f,c['native_certificate'],c['domain_theorems'],base,attempts,extras,classification,trust)
 for key in ['hypotheses','new_trust_rows','required_obligations','edges','call_domain_certificates','support']:assert c[key]==expected[key],key
 return True
