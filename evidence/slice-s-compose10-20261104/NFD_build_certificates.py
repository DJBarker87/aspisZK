"""Complete exact new certificates. No promotion for missing native/Lean sets."""
from pathlib import Path
import json,re
import NFD_validate as v
import NFD_bridge_checks as b
E=v.E;R=v.R

def ref(p):return dict(path=str(p.relative_to(R)),sha256=v.sha(p.read_bytes()))
def theorem(name,a,folder=E,prefix='NFD_'):
 p=folder/a/(prefix+'SOURCE.lean.txt');s=p.read_text();start=s.index('theorem '+name.rsplit('.',1)[1]+' ');end=start+re.search(r'\s:=\s',s[start:]).start();statement=s[start:end].rstrip()
 return dict(name=name,source=ref(p),receipt=ref(folder/a/'receipt.json'),snapshot_path=prefix+'generated/'+name.rsplit('.',1)[0]+'.lean',statement=statement,statement_sha256=v.sha(statement.encode()))
def build(base):
 f=b.REQUEST;by={}
 for row in base['rows']:by.setdefault(row['function'],[]).append(row)
 table={'NFD_RequestOracle':'NFD_L003','NFD_RequestDomains':'NFD_L004','NFD_RequestProjection':'NFD_L005'}|{f'NFD_RequestField{i:02}':f'NFD_L{6+i:03}' for i in range(14)}
 thms=[theorem(n,table[n.rsplit('.',1)[0]]) for n in b.THEOREMS]
 pairs=[[f'NFD_K{3+2*i:03}',f'NFD_K{4+2*i:03}' if i!=11 else 'NFD_K034'] for i in range(14)]
 attempts=[a for pair in pairs for a in pair]+['NFD_K031','NFD_K032','NFD_K033']
 support={E/'NFD_REQUEST_TEMPLATE.json',E/'NFD_REQUEST_REFERENCE.json'}
 for a in attempts:
  names=[a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-shape.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'-frozen-identity.json',a+'-rule16-check.json',a+'-metadata-pin.json',a+'-NFD_native_contracts.patch',a+'-NFD_oracle.patch']
  archive=a+'-inputs.json' if (E/(a+'-inputs.json.xz')).exists() else 'NFD_SOURCE_HISTORY.json';names += [archive+'.xz',archive+'.sha256'];support.update(E/n for n in names)
 c=dict(id='NFD_request',kind='root-composition',subject=f,frozen_revision=base['frozen_revision'],native_certificate=dict(function=f,complete=True,domain='all valid immutable slices; every raw byte and error path; no canonicality restriction',pairs=pairs,controls=['NFD_K033'],length_partition=['NFD_K031','NFD_K032']),domain_theorems=thms,physical_theorems=thms,support=[ref(p) for p in sorted(support)],required_obligations=[o['id'] for r in by[f] for o in r['caller_domain_obligations']],edges=[e for e in b.SPEC['internal_edges'] if e.startswith(f+' -> ')],hypotheses=[f+'.PacketDomain',f+'.PhysicalInterpretation','RuntimePersistence','CompositionTrustOptionA'],new_trust_rows=[],inner_hypotheses_remaining=[],trust_classification='P6/D188 option A reclassification',reference_source=b.request_reference(),call_domain_certificates={})
 c.update({k:True for k in ['exact_callsite',*b.FLAGS]})
 for edge in c['edges']:
  g=edge.split(' -> ')[1];obs=[o for r in by[f] for o in r['caller_domain_obligations'] if o.get('callee')==g]
  names=list(dict.fromkeys([h for o in obs for h in o['required_named_hypotheses']]+[h['name'] for r in by[g] for h in r['named_hypotheses']]))
  d=dict(subject=edge,classification='native U8 discriminator1/2, exact emitted enum carrier' if g.endswith('::transition_kind') else 'same immutable216-byte suffix; all-raw decoder domain; exact returned record/error carrier',selected_callee_claims=list(dict.fromkeys(x for r in by[g] for x in r['selected_claims'])),inner_names_discharged=names,domain_theorems=thms,physical_theorems=thms,inner_hypotheses_remaining=[])
  d.update({k:True for k in b.FLAGS});c['call_domain_certificates'][edge]=d
 c['semantic_review_sha256']=v.sha(json.dumps(c,sort_keys=True).encode())
 assert v.certificate(c,f,base)
 return dict(inherits='evidence/slice-s-compose9-20261104/NEY_LEDGER_DELTA.json',NFD_certificates={f:c})
if __name__=='__main__':
 base=dict(rows=v.read(v.inherited.E/'NEY_CHECKED_ROWS.json'),frozen_revision=b.REV,trust_rows=[])
 packet=build(base);(E/'NFD_LEDGER_DELTA.json').write_text(json.dumps(packet,indent=1)+'\n')
 out=v.compose(base,packet);(E/'NFD_CHECKED_ROWS.json').write_text(json.dumps(out['rows'],indent=1)+'\n')
 print(json.dumps(dict(request_status=[r['composed_status'] for r in out['rows'] if r['function']==b.REQUEST],slice_closed=sum(r['composed_status']=='CLOSED' for r in out['rows']))))
