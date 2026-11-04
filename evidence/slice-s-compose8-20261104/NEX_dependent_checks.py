"""Call-domain closure on already conditional raw decoder rows."""
import copy,json
import NEX_raw_checks as raw
F=raw.F['afterdecode']
THEOREMS=['NEX_AfterDecodeOracle.result_state_effects','NEX_ReadDomains.after_window','NEX_ReadDomains.after_scalar','NEX_ReadDomains.disjoint','NEX_DigestCallDomains.after_digest','NEX_DigestCallDomains.exact_after','NEX_FirstError.bounded','NEX_FirstError.before','NEX_FirstError.at_error','NEX_AfterstateBox.value_ext']
def check(c,ledger):
 n=c['native_certificate'];assert n['function']==F and n['family']=='afterdecode'
 assert n['domain']=='every live688-byte input; arbitrary full AtomicStatementError and validator Results; all bytes and fields unrestricted'
 assert n['inner_hypotheses_remaining']==[] and n['box_ruling_aa'] is False
 assert raw.complete('afterdecode',n['config'])
 assert [t['name'] for t in c['domain_theorems']]==THEOREMS
 assert c['domain_theorems']==c['physical_theorems']
 # Every historical model/receipt/subject/axiom gate applies unchanged.
 import NED_validate,NEJ_validate
 assert NED_validate.certificate(c,c['subject'],ledger,{c['subject']:c['semantic_review_sha256']})
 assert NEJ_validate.call_domain(c,c['subject'],ledger)
 assert c['theorems']==c['domain_theorems'] and c['native_association']==c['support']
 expected=set()
 for pair in n['config']['pairs']:
  for a in pair:expected.add(a)
 expected.update(n['config']['controls'].values())
 actual={r['path'].split('/')[-2] for r in c['support'] if r['path'].endswith('/receipt.json')}
 assert actual==expected
 return True

def compose(base,out,packet,reviewed,v):
 result=copy.deepcopy(out);rows=[r for r in result['rows'] if r['function']==F]
 n=packet.get('NEX_call_domain_additions',{}).get(F)
 if not n:return result
 required={F:packet.get('members',{}).get(F)}
 for row in rows:
  required.update({F+'::'+h['name']:packet.get('hypotheses',{}).get(F+'::'+h['name']) for h in row['named_hypotheses']})
  required.update({F+' -> '+o['callee'] if 'callee' in o else o['id']:(packet.get('edges',{}).get(F+' -> '+o['callee']) if 'callee' in o else packet.get('externals',{}).get(o['id'])) for o in row['caller_domain_obligations']})
 try:
  for subject,c in required.items():
   assert v.certificate(c,subject,base,reviewed)
   assert c['native_certificate']==n
  assert rows and all(r['bridge_status']=='CLOSED-CONDITIONAL' and r['selected_claims'] for r in rows)
  by={}
  for row in result['rows']:by.setdefault(row['function'],[]).append(row)
  assert all(all(q['composed_status']=='CLOSED' for q in by[g]) for r in rows for g in r['canonical_callees'])
  assert not any(r['open_transitive_dependencies'] for r in rows)
 except (AssertionError,KeyError,TypeError,ValueError,OSError):return result
 for row in rows:
  for h in row['named_hypotheses']:h['discharged_by']=required[F+'::'+h['name']]['id']
  for o in row['caller_domain_obligations']:
   subject=F+' -> '+o['callee'] if 'callee' in o else o['id'];o.update(status='CLOSED',discharged_by=required[subject]['id'])
  row.update(composed_status='CLOSED',composed_reason='NEX full-Result native call domains, closed exact/digest/validator children, factored source theorem and complete indexed frame')
 # No source/model/claim/alternative/obligation statement is rewritten.
 allowed={'named_hypotheses','caller_domain_obligations','composed_status','composed_reason'}
 for a,b in zip(result['rows'],out['rows']):
  if b['function']!=F:assert a==b
  else:
   assert {k:w for k,w in a.items() if k not in allowed}=={k:w for k,w in b.items() if k not in allowed}
   for x,y in zip(a['caller_domain_obligations'],b['caller_domain_obligations']):assert {k:w for k,w in x.items() if k not in ['status','discharged_by']}=={k:w for k,w in y.items() if k not in ['status','discharged_by']}
 return result
